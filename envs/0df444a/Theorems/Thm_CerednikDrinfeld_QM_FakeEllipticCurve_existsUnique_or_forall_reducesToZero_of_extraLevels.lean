-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_or_forall_reducesToZero_of_extraLevels
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_or_forall_reducesToZero_of_extraLevels
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/21b9a3b5-1a19-5e3c-9e18-5549926ca5d2
-- title:
--   Ordinary–supersingular dichotomy for the ℓ+1 extra levels
-- statement:
--   Fix rationals $a,b$, a $\mathbb Z$-submodule $\Lambda\subseteq\mathbb H[\mathbb Q,a,b]$ and a natural number $N$. Let $O$ be a valuation subring of $\overline{\mathbb Q}$ and $\ell$ a prime with $\ell$ a nonunit of $O$, and assume $\ell\nmid N$, that $\Lambda$ is an order maximal among orders, and that for primes $q,q'$ the algebra $\mathbb H[\mathbb Q,a,b]$ satisfies $0<a$ or $0<b$ and its completion at a height-one prime $v$ of $\mathcal O_{\mathbb Q}$ is a division algebra exactly when $q\in v$ or $q'\in v$, with $\ell\neq q,q'$. Let $\mathcal A$, $E$, $\bar A$ be fake elliptic curves of level $(\Lambda,N)$ over $O$, over $\overline{\mathbb Q}$ and over the residue field of $O$, and let $g_E:E.A\to\mathcal A.A$ and $g:\bar A.A\to\mathcal A.A$ exhibit $E$ and $\bar A$ as the pullbacks of $\mathcal A$ along $O\hookrightarrow\overline{\mathbb Q}$ and along $O\to O/\mathfrak m$, compatibly with the relative group laws and with the $\Lambda$-actions. Let $K_0,\dots,K_\ell$ be extra levels of $E$ at $\ell$ (closed subschemes of $E.A$, finite flat of rank $\ell^2$, closed under the group law, $\Lambda$-stable, killed by $\ell$, disjoint from $E.\mathrm{lev}$, with geometric fibres $(\mathbb Z/\ell)^2$), pairwise distinguished by the sets of $\overline{\mathbb Q}$-points factoring through them. Call a $\overline{\mathbb Q}$-point $x$ of $E$ reducing to zero if some $O$-point of $\mathcal A$ restricts to $x\circ g_E$ generically and to the origin of $\bar A$ composed with $g$ on the closed fibre. Then either exactly one index $i_0$ has all points factoring through $K_{i_0}$ reducing to zero, or all points of all $K_i$ reduce to zero and every $\ell$-torsion point of $\bar A$ over the residue field is the identity.
--
--   This is the ordinary/supersingular dichotomy for the reduction of the $\ell+1$ cyclic level-$\ell$ structures on a fake elliptic curve at a place above $\ell$: the kernel of reduction on $\ell$-torsion either meets the extra levels in exactly one of them or swallows them all, the latter forcing the special fibre to have no rational $\ell$-torsion. It feeds the Eichler–Shimura style computation of the correspondence on the Shimura curve model in terms of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_existsUnique_or_forall_reducesToZero_of_extraLevels.lean

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM
open NeronModelInfra
open CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.existsUnique_or_forall_reducesToZero_of_extraLevels
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) [Fact ℓ.Prime] (hO : O.LiesOverPrime ℓ) (hℓN : ¬ ℓ ∣ N)
    (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (𝒜 : FakeEllipticCurve Λ N ↥O) (E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (Abar : FakeEllipticCurve Λ N (IsLocalRing.ResidueField ↥O))

    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)

    (gbar : Abar.A ⟶ 𝒜.A)
    (hgbar : CategoryTheory.IsPullback gbar Abar.f 𝒜.f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))))
    (hgbar_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O))) (P Q : SchemeHomOver t' Abar.f),
      (Abar.L.mul t' P Q).1 ≫ gbar =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)))
          ⟨P.1 ≫ gbar, by rw [Category.assoc, hgbar.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gbar, by rw [Category.assoc, hgbar.w, ← Category.assoc, Q.2]⟩).1)
    (hgbar_act : ∀ x : ↥Λ, Abar.act x ≫ gbar = gbar ≫ 𝒜.act x)

    (K : Fin (ℓ + 1) → E.ExtraLevel ℓ)
    (hK : ∀ i j : Fin (ℓ + 1),
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough (K i).levK x ↔ FactorsThrough (K j).levK x) → i = j) :

    let RedZero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f → Prop := fun x =>
      ∃ xt : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥O))) 𝒜.f,
        Spec.map (CommRingCat.ofHom O.subtype) ≫ xt.1 = x.1 ≫ gE ∧
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ xt.1 =
          (Abar.L.one (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O))))).1 ≫ gbar
    (∃! i₀ : Fin (ℓ + 1), ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f, FactorsThrough (K i₀).levK x → RedZero x) ∨
    ((∀ (i : Fin (ℓ + 1)) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (AlgebraicClosure ℚ)))) E.f), FactorsThrough (K i).levK x → RedZero x) ∧
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O)))) Abar.f,
        nsmulPt Abar.L (𝟙 _) ℓ P = Abar.L.one (𝟙 _) → P = Abar.L.one (𝟙 _)) := by sorry
