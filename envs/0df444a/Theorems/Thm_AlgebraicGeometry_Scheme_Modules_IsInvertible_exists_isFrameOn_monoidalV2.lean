-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/690f63e3-497c-537b-a6e2-12b7c830a931
-- title:
--   Invertible 𝒪_X-modules admit local frames
-- statement:
--   Let $X$ be a scheme and let $M$ be an object of `X.Modules`, i.e. a sheaf of modules over the structure sheaf of $X$. Assume `hM`, the property `IsInvertible M`, which asserts that for every point of $X$ there is an open $U$ containing it such that the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules, to the unit object (the structure sheaf of $U$ regarded as a module over itself). Let $x$ be a point of $X$. Then there exist an open $U$ of $X$ and a section $s \in \Gamma(M, U)$ such that $x \in U$ and `IsFrameOn s U` holds, that is: for every open $W$ with $W \le U$, the map $\Gamma(X, W) \to \Gamma(M, W)$ sending $g$ to $g \cdot (s|_W)$, where $s|_W$ is the image of $s$ under the restriction map of the presheaf underlying $M$, is bijective. (In `IsFrameOn s U` the ambient open and the frame domain are taken to be the same, so the two inequalities $W \le U$ occurring in the definition coincide.)
--
--   This is the statement that an invertible sheaf of modules on a scheme has, near each point, a nowhere-vanishing generating section — a local frame trivialising $M$ over an open neighbourhood — and it is the converse direction to the criterion for invertibility by existence of local frames. It is used in the construction of section rings of graded $\mathcal{O}$-algebras and in the comparison of invertible modules with their vanishing ideals, both feeding into the treatment of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M)
    (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ AlgebraicGeometry.Scheme.Modules.IsFrameOn s U := by sorry
