-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/33d24d25-8a93-5431-a56c-fc007eb94108
-- title:
--   Existence of the Atkin–Lehner quotient at ̄ r with universal property
-- statement:
--   Fix primes $r$ and $\bar r$ and a nonzero level $N$, with $\bar r \neq r$ and $\bar r \nmid N$, and rationals $a,b$ such that `IsIndefiniteRamifiedExactlyAt a b r rbar` holds: $a>0$ or $b>0$, and for every height-one prime $v$ of $\mathcal O_{\mathbb Q}$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda$ be a $\mathbb Z$-submodule of $\mathbb H[\mathbb Q,a,b]$ that is an order maximal among orders for inclusion, let $k_0$ be an algebraically closed field of characteristic $r$, and let $A_0$ be a fake elliptic curve of level $N$ with $\Lambda$-action over $k_0$. The assertion is that there exist a further fake elliptic curve $A_{0,w}$ over $k_0$ and morphisms $a_w : A_0.A \to A_{0,w}.A$ and $a_w' : A_{0,w}.A \to A_0.A$ over $\mathrm{Spec}\,k_0$ such that `IsAtkinLehnerQuotientVia rbar` holds for the pair $(a_w,a_w')$ — both are homomorphisms for the relative group laws on $T$-points, both commute with the $\Lambda$-actions, their two composites are the action of $\bar r$ whenever $\bar r \in \Lambda$, a $T$-point $P$ of $A_0$ is killed by $a_w$ precisely when $\mathrm{act}(m)$ kills $P$ for every $m \in \Lambda$ with $m\,\bar m = \bar r\,n$ for some integer $n$, and $a_w$ carries points factoring through $A_0.\mathrm{lev}$ to points factoring through $A_{0,w}.\mathrm{lev}$ — and moreover that $a_w$ is an epimorphism of schemes, and that for every endomorphism $\varphi$ of $A_0.A$ over $\mathrm{Spec}\,k_0$ which is a homomorphism for $A_0.L$ on all $T$-points and which kills every $T$-point annihilated by all such $m$, there is a unique morphism $\chi : A_{0,w}.A \to A_0.A$ over $\mathrm{Spec}\,k_0$ with $a_w$ followed by $\chi$ equal to $\varphi$ and with $\chi$ a homomorphism from $A_{0,w}.L$ to $A_0.L$.
--
--   This is the construction, in characteristic $r$ and for fake elliptic curves with $\Lambda$-action, of the Atkin–Lehner quotient by the $\mathfrak P_{\bar r}$-torsion, together with the statement that the quotient map is an epimorphism and is universal among group-law homomorphisms out of $A_0$ killing that torsion. It is used in the Čerednik–Drinfeld analysis of the special fibre to produce the isogeny pair attached to an endomorphism which is multiplication by the Atkin–Lehner element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotientVia_epi_and_forall_existsUnique_comp_eq
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrbarN : ¬ rbar ∣ N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀) :
    ∃ (A₀w : FakeEllipticCurve Λ N k₀)
      (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f),
      FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw' ∧ Epi aw ∧
      ∀ (φ : A₀.A ⟶ A₀.A) (hφ : φ ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ hφ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P : SchemeHomOver t A₀.f),
          (∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((rbar : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
          pushPt (A₀.act m) (A₀.act_over m) P = A₀.L.one t) → mapPt φ hφ P = A₀.L.one t) →
        ∃! χ : SchemeHomOver A₀w.f A₀.f, aw ≫ χ.1 = φ ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀w.f),
        mapPt χ.1 χ.2 (A₀w.L.mul t P Q) = A₀.L.mul t (mapPt χ.1 χ.2 P) (mapPt χ.1 χ.2 Q)) := by sorry
