-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_regions_exhaustive
-- name    : DriftVarCtrl.FixedLB.regions_exhaustive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:23:14.69988+00:00
-- url     : https://prove2.me/theorems/30fe3060-6661-4c1f-b7a6-bc3f3cdf37cc
-- title:
--   §4, p. 13 — the regions (7)–(10) are collectively exhaustive
-- statement:
--   Assume $v_1 < v_2$. For every choice of the model parameters, at least one of the conditions (7), (8), (9), (10) of Theorem 2 holds:
--   $$(7)\ \lor\ (8)\ \lor\ (9)\ \lor\ (10).$$
--
--   Geometrically, the four lines $\Delta h_2 = d_1^L\Delta h_1$, $\Delta h_2 = d_1^U\Delta h_1$, $\Delta h_2 = d_2^L\Delta h_1$, $\Delta h_2 = d_2^U\Delta h_1$ through $(h_1^*,h_2^*)$ split the cost plane into regions that cover it. Combined with Theorem 2, every cost pair admits an optimal policy with at most two intervals.
--
--   **Formalization Note.** The page calls the regions "mutually exclusive"; at $\Delta h_1 = \Delta h_2 = 0$ both (7) and (8) hold, so only exhaustiveness is stated. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 13, §4, Visual Interpretation of Theorem 2

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Constants

namespace DriftVarCtrl.FixedLB

/-- §4, "Visual Interpretation of Theorem 2" (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 13): the lines of (7)–(10) divide the
`(h₁, h₂)` plane into four collectively exhaustive regions, i.e. one of (7)–(10) always holds.

Formalization Note: the page also says "mutually exclusive"; that fails at `Δh₁ = Δh₂ = 0`, where (7)
and (8) both hold, so only exhaustiveness is stated. The standing `v₁ < v₂` (p. 12) is the hypothesis
`hv`. -/
theorem regions_exhaustive (p : Params) (hv : v p .one < v p .two) :
    cond7 p ∨ cond8 p ∨ cond9 p ∨ cond10 p := by sorry

end DriftVarCtrl.FixedLB
