-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
-- name    : AlgebraicGeometry.Scheme.Hom.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f5a42f20-de29-5c82-8b31-3d0b7e680f41
-- title:
--   Smooth of relative dimension d: Ω¹ locally free, ωᵈ invertible
-- statement:
--   Let $A$ be a commutative ring, $X$ a scheme, and $f \colon X \to \operatorname{Spec} A$ a morphism of schemes (all in a single universe), let $d$ be a natural number, and assume $f$ is smooth of relative dimension $d$ in Mathlib's sense. The conclusion is a conjunction. First, the sheaf of modules `f.kaehler` — the sheafification of the presheaf of relative differentials of the ring map underlying $f$, i.e. $\Omega^1_{X/A}$ — is locally free of rank $d$ in the project's sense: for every point $x$ of $X$ there is an open $U \subseteq X$ with $x \in U$ such that the pullback of $\Omega^1_{X/A}$ along the inclusion $U \hookrightarrow X$ admits an isomorphism (the type of such isomorphisms is nonempty) to the free sheaf of modules on the index type $\mathrm{ULift}(\mathrm{Fin}\,d)$. Secondly, `f.topDifferentials d`, defined as the $d$-th determinant $\det_d \Omega^1_{X/A} = \bigwedge^d \Omega^1_{X/A}$, is locally free of rank $1$ in the same sense, i.e. locally isomorphic to the free sheaf of rank one.
--
--   This is the standard local structure result for smooth morphisms over an affine base (EGA IV 17.2.3): the sheaf of relative differentials of a morphism smooth of relative dimension $d$ is locally free of rank $d$, whence its top exterior power is a line bundle. It supplies the invertible sheaf $\omega^d_{X/A}$ used to produce local frames for top differentials in the treatment of relative group laws on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_KaehlerModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    Scheme.Modules.IsLocallyFreeOfRank d f.kaehler ∧
      Scheme.Modules.IsLocallyFreeOfRank 1 (f.topDifferentials d) := by sorry
