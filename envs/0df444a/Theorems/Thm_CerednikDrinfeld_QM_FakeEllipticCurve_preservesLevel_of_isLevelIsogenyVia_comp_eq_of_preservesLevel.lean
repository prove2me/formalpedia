-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isLevelIsogenyVia_comp_eq_of_preservesLevel
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isLevelIsogenyVia_comp_eq_of_preservesLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/ea92d3e6-3696-501f-ae07-5d2af52efbc2
-- title:
--   Level preservation descends to the second factor of an ℓ-isogeny
-- statement:
--   Fix natural numbers $r$, $\bar r$ prime with $\bar r \neq r$ and $N \neq 0$, rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($a>0$ or $b>0$) and, at each finite place $v$ of $\mathbb{Q}$, its completion is a division algebra exactly when $v$ divides $r$ or $\bar r$, and a maximal order $\Lambda$ (an order contained in no strictly larger order). Let $k_0$ be an algebraically closed field of characteristic $r$, and let $A_0, A_{0s}$ be fake elliptic curves over $k_0$ for $(\Lambda, N)$. Let $\ell$ be a prime with $\ell \neq r$ and $C_0$ an extra level-$\ell$ structure on $A_0$. Let $as : A_0.A \to A_{0s}.A$ and $as' : A_{0s}.A \to A_0.A$ be morphisms over $\operatorname{Spec} k_0$ forming a level-$\ell$ isogeny for $(A_0,C_0)$ and $A_{0s}$: both are additive for the relative group laws on points, commute with the $\Lambda$-actions, their two composites are the action of $\ell \in \Lambda$, the points killed by $as$ are exactly those factoring through $C_0.levK$, and $as$ sends points factoring through $A_0.lev$ to points factoring through $A_{0s}.lev$. Let $f$ be an endomorphism of $A_0.A$ over $k_0$ preserving the level, i.e. carrying any $T$-point factoring through $A_0.lev$ to one factoring through $A_0.lev$, and let $bs : A_{0s}.A \to A_0.A$ over $k_0$ be additive on points with $as$ followed by $bs$ equal to $f$. The conclusion is that $bs$ preserves the level: for every $t : T \to \operatorname{Spec} k_0$ and every $T$-point $Q$ of $A_{0s}$ over $t$ factoring through $A_{0s}.lev$, the point $Q$ followed by $bs$ factors through $A_0.lev$.
--
--   This is the step asserting that if a level-preserving endomorphism of a fake elliptic curve factors as a level-$\ell$ isogeny followed by a further morphism, then that second factor again preserves the level-$N$ structure. It feeds the construction of Hecke correspondences in characteristic $r$, being cited in the production of an extra level structure and level isogeny factoring a given endomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_of_isLevelIsogenyVia_comp_eq_of_preservesLevel.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_of_isLevelIsogenyVia_comp_eq_of_preservesLevel
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ A₀s : FakeEllipticCurve Λ N k₀)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r) (C₀ : A₀.ExtraLevel ℓ)
    (as : A₀.A ⟶ A₀s.A) (has : as ≫ A₀s.f = A₀.f) (as' : A₀s.A ⟶ A₀.A) (has' : as' ≫ A₀.f = A₀s.f)
    (hLI : FakeEllipticCurve.IsLevelIsogenyVia ℓ ⟨A₀, C₀⟩ A₀s as has as' has')
    (f : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf_lev : FakeEllipticCurve.PreservesLevel A₀ A₀ f hf)
    (bs : A₀s.A ⟶ A₀.A) (hbs : bs ≫ A₀.f = A₀s.f)
    (hbs_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀s.f),
      mapPt bs hbs (A₀s.L.mul t P Q) = A₀.L.mul t (mapPt bs hbs P) (mapPt bs hbs Q))
    (hcomp : as ≫ bs = f) :
    FakeEllipticCurve.PreservesLevel A₀s A₀ bs hbs := by sorry
