-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_of_isProper_of_isIntegral
-- name    : AlgebraicGeometry.Scheme.bijective_algebraMap_sections_of_isProper_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7aab1ebb-c99b-5549-ac3f-d1fd0f7e2ab5
-- title:
--   Global sections of a proper integral scheme over algebraically closed k
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme, and let $\pi \colon X \to \operatorname{Spec}(k)$ be a morphism which is proper and for which $X$ is an integral scheme (in Mathlib's sense of `IsIntegral`). Equip the ring $\Gamma(X,\top)$ of global sections with the $k$-algebra structure `Scheme.TwoAffineOpenCover.algebraOfHom π ⊤`, that is, the algebra structure attached to the ring homomorphism $k \to \Gamma(X,\top)$ obtained by composing the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec}(k),\top) \cong k$ with the map $\pi.appLE\ \top\ \top$ induced by $\pi$ on global sections. The assertion is that the resulting structure map $\mathrm{algebraMap}\ k\ \Gamma(X,\top)$ is bijective as a function, i.e. that every global regular function on $X$ is the image of a unique scalar in $k$. Here $\top$ denotes the largest open subscheme of $X$ in each case, so no restriction to a smaller open is involved.
--
--   This is the standard statement that a proper integral scheme over an algebraically closed field has only constant global regular functions, $\Gamma(X,\mathcal O_X) = k$. It is used in the treatment of relative Picard functors and line bundles on curves, for instance in recognising when a rigidified line bundle is trivial and in the analysis of degenerations of smooth curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_of_isProper_of_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.bijective_algebraMap_sections_of_isProper_of_isIntegral
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of k))
    [IsProper π] [IsIntegral X] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
    Function.Bijective (algebraMap k Γ(X, ⊤)) := by sorry
