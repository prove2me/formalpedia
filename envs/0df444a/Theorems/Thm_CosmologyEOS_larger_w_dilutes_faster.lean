-- Prove2me | Theorems.Thm_CosmologyEOS_larger_w_dilutes_faster
-- name    : CosmologyEOS.larger_w_dilutes_faster
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:37:32.173975+00:00
-- url     : https://prove2.me/theorems/42094a9c-d32d-4188-bd75-92f5de067bb7
-- title:
--   Fluids with larger $w$ disappear faster
-- statement:
--   Let $w_1<w_2$. Let $a$ be the scale factor and let $(\varepsilon_1,p_1)$, $(\varepsilon_2,p_2)$ be two perfect fluids in the same universe: all functions are differentiable at all times, $a>0$, $\varepsilon_1>0$, $p_i = w_i\varepsilon_i$, and each fluid satisfies the fluid equation $\dot\varepsilon_i = -3\frac{\dot a}{a}(\varepsilon_i+p_i)$. If the universe expands without bound, $a(t)\to\infty$ as $t\to\infty$, then
--
--   $$\frac{\varepsilon_2(t)}{\varepsilon_1(t)} \longrightarrow 0 \qquad (t\to\infty).$$
--
--   So the fluid with the larger equation of state becomes negligible relative to the other.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'Fluids'

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem larger_w_dilutes_faster (w₁ w₂ : ℝ) (hw : w₁ < w₂) (a ε₁ ε₂ p₁ p₂ : ℝ → ℝ)
    (ha_diff : ∀ t, DifferentiableAt ℝ a t)
    (hε₁_diff : ∀ t, DifferentiableAt ℝ ε₁ t)
    (hε₂_diff : ∀ t, DifferentiableAt ℝ ε₂ t)
    (ha_pos : ∀ t, 0 < a t)
    (hε₁_pos : ∀ t, 0 < ε₁ t)
    (heos₁ : ∀ t, p₁ t = w₁ * ε₁ t) (heos₂ : ∀ t, p₂ t = w₂ * ε₂ t)
    (hfluid₁ : ∀ t, FluidEquation a ε₁ p₁ t) (hfluid₂ : ∀ t, FluidEquation a ε₂ p₂ t)
    (hexpand : Tendsto a atTop atTop) :
    Tendsto (fun t => ε₂ t / ε₁ t) atTop (𝓝 0) := by
  sorry

end CosmologyEOS
