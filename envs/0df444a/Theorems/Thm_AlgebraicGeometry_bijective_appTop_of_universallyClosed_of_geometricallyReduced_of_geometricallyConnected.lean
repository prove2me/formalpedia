-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
-- name    : AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/c3e9872a-ce2a-5609-88c6-2719e6851822
-- title:
--   K → Γ(X,mathcal O_X) bijective for universally closed X
-- statement:
--   Let $K$ be a field (a type in a fixed universe, with its field structure) and let $X$ be a scheme in that universe, equipped with a morphism $f \colon X \to \operatorname{Spec} K$, where $\operatorname{Spec} K$ is the spectrum of the commutative ring underlying $K$. Three hypotheses are imposed on $f$ as instances: `UniversallyClosed f`, i.e. every base change of $f$ is a closed map; `GeometricallyReduced f` and `GeometricallyConnected f`, the assertions that $f$ is geometrically reduced and geometrically connected, which for the base $\operatorname{Spec} K$ amount to reducedness, respectively connectedness, of the base changes $X \times_{\operatorname{Spec} K} \operatorname{Spec} K'$ along field extensions $K'/K$. The conclusion is that the ring homomorphism $f$`.appTop`, the map induced by $f$ on sections over the whole space, from $\Gamma(\operatorname{Spec} K, \mathcal O) = K$ to $\Gamma(X, \mathcal O_X)$, is bijective as a function. Thus every global regular function on $X$ comes from a unique element of $K$, i.e. $H^0(X, \mathcal O_X) = K$; in particular no finite-type or flatness hypothesis is required, and the empty scheme is excluded by connectedness.
--
--   This is the classical statement that a universally closed (for instance proper), geometrically reduced and geometrically connected scheme over a field has only constant global functions, isolated over a base field. It serves as the fibrewise input for the results asserting $\mathcal O_S \xrightarrow{\sim} f_*\mathcal O_X$ for proper flat morphisms with geometrically reduced and connected fibres, and for the descent of geometric connectedness through such families.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [UniversallyClosed f] [GeometricallyReduced f] [GeometricallyConnected f] :
    Function.Bijective f.appTop := by sorry
