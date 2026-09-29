-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn
-- name    : AlgebraicGeometry.Scheme.Modules.isInvertible_of_forall_exists_isFrameOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/cc9257ef-cb39-5af3-ac9f-17041eada5e8
-- title:
--   Locally framed modules on a scheme are invertible
-- statement:
--   Let $X$ be a scheme and let $M$ be a sheaf of modules over the structure sheaf of $X$ (an object of `X.Modules`). Assume that for every point $x$ of $X$ there exist an open subset $U \subseteq X$ and a section $s \in \Gamma(M, U)$ with $x \in U$ such that `IsFrameOn s U` holds, that is: for every open $W$ with $W \le U$ (the second comparison $W \le U$ being the same condition here), the map $\Gamma(X, W) \to \Gamma(M, W)$ sending $g$ to $g \cdot (s|_W)$, where $s|_W$ is the image of $s$ under the restriction map of the presheaf underlying $M$, is bijective. The conclusion is `IsInvertible M`: for every point $x$ of $X$ there is an open subset $U$ containing $x$ such that the pullback of $M$ along the open immersion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules on $U$, to the unit object $\mathcal{O}_U$ given by the sheaf of rings of $U$; equivalently, $M$ is locally isomorphic to the structure sheaf.
--
--   This is the passage from the generator-style description of a line bundle (a local section whose multiples exhaust the module, freely) to the isomorphism-style one ($M$ locally isomorphic to $\mathcal{O}_X$). It is the standard route by which modules presented by explicit local frames are recognised as invertible, and it is used in the construction of invertible sheaves by gluing cocycle data, in the comparison of invertible sheaves across a Milnor square, and in the surjectivity of the deformation class map for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_of_forall_exists_isFrameOn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isInvertible_of_forall_exists_isFrameOn
    {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (h : ∀ x : X, ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ AlgebraicGeometry.Scheme.Modules.IsFrameOn s U) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible M := by sorry
