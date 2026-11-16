-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_congr
-- name    : FiniteEnergyPlane.expDecayCInfty_congr
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-15T16:08:37.365453+00:00
-- url     : https://prove2.me/theorems/3927236d-1b0f-4918-82a0-900243289be3
-- title:
--   Exponential C-infinity decay on a cylindrical end depends only on the far end
-- statement:
--   Let $F$ be a real normed space, $f,g:\mathbb R\times\mathbb R\to F$, $b,s_0\in\mathbb R$. Suppose $f$ decays like $e^{-bs}$ in $C^\infty$ on the end $s\to+\infty$ (smooth on some $(s_1,\infty)\times\mathbb R$, and for every $m$ there are $C,s_2$ with $\|D^mf(s,t)\|\le Ce^{-bs}$ for $s\ge s_2$ and all $t$), and $g(s,t)=f(s,t)$ for all $s>s_0$ and all $t$. Then $g$ decays like $e^{-bs}$ in $C^\infty$.
--
--   This lets one change a decaying function on any bounded-below region of the cylinder (for example, replace it by a globally defined formula that agrees with it far out) without losing the decay.
--
--   Formalization Note: decay is `ExpDecayCInfty f b`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞` exponential decay on a cylindrical end only depends on the function far out: if `f`
decays like `e^{-bs}` in `C^∞` and `g (s, t) = f (s, t)` for all `s > s₀` and all `t`, then `g`
decays like `e^{-bs}` in `C^∞`. -/
theorem expDecayCInfty_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ × ℝ → F} {b s₀ : ℝ} (hf : ExpDecayCInfty f b)
    (h : ∀ s > s₀, ∀ t, g (s, t) = f (s, t)) : ExpDecayCInfty g b := by
  sorry

end FiniteEnergyPlane
