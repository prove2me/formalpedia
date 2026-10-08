-- Prove2me | Theorems.Thm_ContactCalculus_strict_hopf_pullback_intertwines
-- name    : ContactCalculus.strict_hopf_pullback_intertwines
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T10:06:44.80865+00:00
-- url     : https://prove2.me/theorems/4098540b-d176-44d8-b9ba-7d36b92fa407
-- title:
--   Strict pullback of the Hopf family intertwines its Reeb fields
-- statement:
--   Let $S^3$ be the unit sphere in $\mathbb R^4$, and set
--   $$\alpha_t=x_1\,dy_1-y_1\,dx_1+(1+t)(x_2\,dy_2-y_2\,dx_2).$$
--   For $t\ge0$, let $f$ be a smooth ambient map restricting to a bijection of the sphere, with injective tangent differential, and suppose $f^*\alpha_t=\alpha_0$ on its tangent bundle. Then
--   $$Df_y R_0(y)=R_t(f(y))\qquad(y\in S^3),$$
--   where $R_t=(-y_1,y_0,-y_3/(1+t),y_2/(1+t))$. This is the strict contact naturality of the Reeb vector field for Geiges's family, and can be reused to compare its dynamics.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/pdf/math/0307242, Remark 2.21(1), printed p. 15. The displayed Reeb field and its naturality under strict pullback.

import Definitions.Def_GrayStability_HopfFamily
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem ContactCalculus.strict_hopf_pullback_intertwines (t : ℝ) (ht : 0 ≤ t)
    (f : E 4 → E 4) (hf : ContDiff ℝ ∞ f)
    (hbij : Set.BijOn f (levelSet unitSphereEquation) (levelSet unitSphereEquation))
    (hinj : ∀ y ∈ levelSet unitSphereEquation,
      Set.InjOn (fderiv ℝ f y) (tangentSpace unitSphereEquation y))
    (hα : ∀ y ∈ levelSet unitSphereEquation, ∀ v ∈ tangentSpace unitSphereEquation y,
      pullback f (hopfFamily t) y v = hopfFamily 0 y v) :
    ∀ y ∈ levelSet unitSphereEquation,
      fderiv ℝ f y ![-y 1, y 0, -y 3, y 2] =
        ![-(f y) 1, (f y) 0, -(f y) 3 / (1 + t), (f y) 2 / (1 + t)] := by sorry
