-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2
-- name    : AlgebraicGeometry.Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/81418077-a317-517e-afa0-42279a821316
-- title:
--   Irreducible closed subsets lie in or miss a basic open
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme and let $t : X \to \operatorname{Spec} k$ be a proper morphism of schemes. Let $Z \subseteq X$ be a subset of the underlying space of $X$ which is closed and irreducible (in particular nonempty), let $U$ be an open subscheme of $X$ with $Z \subseteq U$, and let $g \in \Gamma(X, U)$ be a section of the structure sheaf over $U$. The conclusion is the disjunction: either $Z$ is contained in the basic open set $X.\mathrm{basicOpen}\, g$, the largest open subset of $U$ on which $g$ is invertible, or $Z$ and $X.\mathrm{basicOpen}\, g$ are disjoint. Equivalently, $g$ vanishes identically on $Z$ or nowhere on $Z$, there being no intermediate case. Nothing beyond properness of $t$ and algebraic closedness of $k$ is assumed about $X$; in particular $X$ is not assumed reduced, separated-by-hand or of finite type beyond what properness of $t$ gives.
--
--   This is the standard consequence of the fact that a proper integral scheme over an algebraically closed field has only constant global functions: a section of the structure sheaf is either identically zero or nowhere zero on an irreducible closed subset. It is used in the construction of the relative Picard functor machinery, where it feeds the analysis of the support of the zero-scheme ideal of a section, via [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.subset_support_zeroSchemeIdeal_or_disjoint_monoidalV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.subset_basicOpen_or_disjoint_of_isProper_of_isIrreducible_monoidalV2
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [IsProper t]
    (Z : Set X) (hZ : IsClosed Z) (hZ' : IsIrreducible Z) (U : X.Opens) (hZU : Z ⊆ U) (g : Γ(X, U)) :
    Z ⊆ X.basicOpen g ∨ Disjoint Z (X.basicOpen g) := by sorry
