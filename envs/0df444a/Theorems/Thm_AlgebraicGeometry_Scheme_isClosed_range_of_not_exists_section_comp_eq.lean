-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq
-- name    : AlgebraicGeometry.Scheme.isClosed_range_of_not_exists_section_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b9ab93c8-8f3e-5a21-8911-78cc5796625b
-- title:
--   Non-extendable K-points over a DVR have closed image
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the `IsDiscreteValuationRing` structure) and let $K$ be a field which is an $R$-algebra and a fraction field of $R$. Let $X$ be a scheme and $f : X \to \operatorname{Spec} R$ a morphism that is separated, locally of finite type and quasi-compact. Let $x : \operatorname{Spec} K \to X$ be a morphism lying over $\operatorname{Spec} R$, in the sense that $x$ followed by $f$ equals $\operatorname{Spec}$ of the structure map $R \to K$. Assume further that $x$ does not extend to a section: there is no morphism $s : \operatorname{Spec} R \to X$ with $s$ followed by $f$ the identity of $\operatorname{Spec} R$ and with $\operatorname{Spec}$ of $R \to K$ followed by $s$ equal to $x$. Then the image of the underlying continuous map of $x$, i.e. the set $\operatorname{range}(x_{\mathrm{top}})$ — a single point of the topological space of $X$, since $\operatorname{Spec} K$ has one point — is closed in $X$.
--
--   This is the complement of the valuative extension criterion: over a discrete valuation ring, a $K$-valued point of a separated, quasi-compact, locally finite-type scheme which fails to extend to an $R$-section is supported at a closed point of $X$. It is used in the construction of relative group laws on models of elliptic curves, where the closedness of such a point allows one to excise it, in [`GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_lift_fst_mul_of_not_exists_section`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_lift_fst_mul_of_not_exists_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isClosed_range_of_not_exists_section_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.isClosed_range_of_not_exists_section_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (hns : ¬ ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x) :
    IsClosed (Set.range x.base) := by sorry
