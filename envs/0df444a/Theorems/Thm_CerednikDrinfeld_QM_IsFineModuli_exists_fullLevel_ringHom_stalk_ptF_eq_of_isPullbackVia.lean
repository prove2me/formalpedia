-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_fullLevel_ringHom_stalk_ptF_eq_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_fullLevel_ringHom_stalk_ptF_eq_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/5cb58a74-4e64-5ea9-8259-117034bd841a
-- title:
--   Full level and moduli point lift to an Artinian deformation
-- statement:
--   Fix primes $q\neq q'$ and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$, the algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ lies over $q$ or $q'$; let $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ be a maximal order (an order — containing $1$, multiplicatively closed, $\mathbb Q$-spanning, finitely generated — maximal among orders), and $m\geq 3$ with $q\nmid m$. Let $\pi_M\colon M\to\operatorname{Spec}\mathbb Z_q$ be a scheme with a family $\mathrm{ptF}$ assigning to each ring $S$, each $s\colon\operatorname{Spec} S\to\operatorname{Spec}\mathbb Z_q$ and each pair consisting of a fake elliptic curve of level $1$ over $S$ with $\Lambda$-action together with a full level-$m$ structure (an $m$-torsion section whose $\Lambda$-translates exhaust the geometric $m$-torsion, with annihilator exactly $m\Lambda$) a morphism over $s$, and assume $(M,\pi_M,\mathrm{ptF})$ is a fine moduli scheme: $\mathrm{ptF}$ is invariant under isomorphism, compatible with base change, surjective, and injective up to isomorphism. Let $y\in M$, let $O$ be a local $\mathbb Z_q$-algebra with $q$ in its maximal ideal and algebraically closed residue field, and let $\bar x\colon\mathcal O_{M,y}\to\mathrm{ResidueField}\,O$ be a ring map with kernel the maximal ideal. Let $u_0$ be a fake elliptic curve with full level-$m$ structure over $\mathrm{ResidueField}\,O$ whose moduli point, taken over the structure map induced by $\mathrm{residue}\circ\mathrm{algebraMap}$, equals $\operatorname{Spec}(\bar x)$ followed by $M.\mathrm{fromSpecStalk}\,y$. Let $A$ be an Artinian local $O$-algebra, $\mathrm{res}_A\colon A\to\mathrm{ResidueField}\,O$ a surjection with $\mathrm{res}_A\circ\mathrm{algebraMap}_{O,A}=\mathrm{residue}\,O$, let $E$ be a fake elliptic curve of level $1$ over $A$, and let $g\colon u_0.1.A\to E.A$ exhibit $u_0.1$ as the base change of $E$ along $\mathrm{res}_A$ in the sense of `IsPullbackVia` (a pullback square compatible with the relative group law, with the $\Lambda$-action, and with factorisation through the level morphism). Then there exist a full level-$m$ structure $P$ on $E$ and a ring homomorphism $\psi\colon\mathcal O_{M,y}\to A$ such that the section of $u_0$ followed by $g$ equals $\operatorname{Spec}(\mathrm{res}_A)$ followed by the section of $P$, $\mathrm{res}_A\circ\psi=\bar x$, and the moduli point of $(E,P)$ over the structure map $\mathrm{algebraMap}_{O,A}\circ\mathrm{algebraMap}_{\mathbb Z_q,O}$ equals $\operatorname{Spec}(\psi)$ followed by $M.\mathrm{fromSpecStalk}\,y$.
--
--   This is the deformation-theoretic step which says that an infinitesimal (Artin local) deformation of the fake elliptic curve at a geometric point of the fine moduli scheme carries a compatible full level-$m$ structure and is therefore classified by a local homomorphism out of the stalk at that point. It feeds the statement that the stalk pro-represents the deformation functor, used in the Čerednik–Drinfeld analysis of the Shimura curve over $\mathbb Z_q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_fullLevel_ringHom_stalk_ptF_eq_of_isPullbackVia.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  IsLocalRing

theorem CerednikDrinfeld.QM.IsFineModuli.exists_fullLevel_ringHom_stalk_ptF_eq_of_isPullbackVia
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m) (hqm : ¬ q ∣ m)
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℤ_[q]))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℤ_[q])),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ 1 m M πM ptF)
    (y : M)

    (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (hqO : algebraMap ℤ_[q] O (q : ℤ_[q]) ∈ maximalIdeal O) [IsAlgClosed (ResidueField O)]

    (xbar : M.presheaf.stalk y →+* ResidueField O)
    (hxbar : RingHom.ker xbar = maximalIdeal (M.presheaf.stalk y))

    (u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m (ResidueField O))
    (hu₀ : (ptF (ResidueField O) (Spec.map (CommRingCat.ofHom ((residue O).comp (algebraMap ℤ_[q] O)))) u₀).1 =
      Spec.map (CommRingCat.ofHom xbar) ≫ M.fromSpecStalk y)

    (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
    (E : FakeEllipticCurve Λ 1 A) (g : u₀.1.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia resA E u₀.1 g) :
    ∃ (P : E.FullLevel m) (ψ : M.presheaf.stalk y →+* A),
      (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom resA) ≫ (P.P).1 ∧
      resA.comp ψ = xbar ∧
      (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) ⟨E, P⟩).1 = (Spec.map (CommRingCat.ofHom ψ) ≫ M.fromSpecStalk y) := by sorry
