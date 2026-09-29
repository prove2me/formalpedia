-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/86589f1a-bfed-5b13-921b-9eda9dea587c
-- title:
--   Invertible modules on the spectrum of a local ring are trivial
-- statement:
--   Let $A$ be a commutative local ring and let $N$ be an object of the category $(\operatorname{Spec} A)$`.Modules` of sheaves of modules over the structure sheaf of the affine scheme $\operatorname{Spec} A$ (written `Spec (CommRingCat.of A)`). Assume that $N$ satisfies the project's invertibility predicate `Scheme.Modules.IsInvertible`, i.e. for every point $x$ of $\operatorname{Spec} A$ there is an open subset $U$ with $x \in U$ such that the pullback of $N$ along the open immersion $U \hookrightarrow \operatorname{Spec} A$ is isomorphic, as a sheaf of modules on $U$, to the unit object `SheafOfModules.unit` of the sheaf of rings of $U$ (no global compatibility or inverse object is required, only this local triviality). The conclusion is that the type of isomorphisms $N \cong \mathbb{1}$ in $(\operatorname{Spec} A)$`.Modules`, where $\mathbb{1}$ is the monoidal unit, is nonempty; that is, $N$ is isomorphic to the structure sheaf itself, an isomorphism being asserted to exist rather than produced as data.
--
--   This is the vanishing of the Picard group of a local ring in its sheaf-theoretic form: a line bundle on the spectrum of a local ring is trivial. It is used throughout the treatment of the relative Picard functor, in particular to rigidify line bundles after pulling back along a section over a local base, and is cited by the statements about representability of the relative Picard functor and about homomorphisms attached to two glued smooth curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing
    {A : Type u} [CommRing A] [IsLocalRing A] {N : (Spec (CommRingCat.of A)).Modules}
    (hN : Scheme.Modules.IsInvertible N) : Nonempty (N ≅ 𝟙_ (Spec (CommRingCat.of A)).Modules) := by sorry
