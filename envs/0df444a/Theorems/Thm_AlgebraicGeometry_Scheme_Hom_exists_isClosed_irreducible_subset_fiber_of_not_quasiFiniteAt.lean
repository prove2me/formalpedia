-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt
-- name    : AlgebraicGeometry.Scheme.Hom.exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/85d05af4-f358-53d6-9081-6e7bec5b3747
-- title:
--   Non-isolated point in the fibre at a non-quasi-finite point
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe), let $f \colon X \to Y$ be a morphism that is locally of finite type, and let $x$ be a point of the underlying space of $X$ at which $f$ fails to be quasi-finite, i.e. the predicate `f.QuasiFiniteAt x` does not hold. Then there exists a subset $Z$ of the underlying topological space of $X$ which is closed, is irreducible (in particular non-empty), contains $x$, is different from the singleton $\{x\}$, and satisfies $Z \subseteq f^{-1}\bigl(\overline{\{f(x)\}}\bigr)$, the preimage under the continuous map `f.base` on underlying spaces of the closure of the singleton $\{f(x)\}$. Thus $x$ lies on an irreducible closed subset of $X$ that is strictly larger than $\{x\}$ and is contained in the preimage of the closure of the image point; note that the containment is formulated with $\overline{\{f(x)\}}$ rather than with the fibre $f^{-1}(f(x))$ itself, which is the correct shape when $f(x)$ is not a closed point of $Y$.
--
--   This is the topological half of the standard characterisation of quasi-finiteness at a point for morphisms locally of finite type: quasi-finite at $x$ means that $x$ is isolated in its fibre, so failure of quasi-finiteness produces a positive-dimensional irreducible closed subset through $x$ inside the fibre. It is used in the finiteness criteria for the structure morphism of a projective presentation of a module, [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff) and [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_forall_pullbackSection_eq_zero_iff`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_toProj_of_forall_pullbackSection_eq_zero_iff), where one must exclude non-isolated points in fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Hom.exists_isClosed_irreducible_subset_fiber_of_not_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) (hx : ¬ f.QuasiFiniteAt x) :
    ∃ Z : Set X, IsClosed Z ∧ IsIrreducible Z ∧ x ∈ Z ∧ Z ≠ {x} ∧
      Z ⊆ f.base ⁻¹' closure {f.base x} := by sorry
