-- Prove2me | Theorems.Thm_AVHighway_DPolicy_eq_20_heavy_traffic_limit
-- name    : AVHighway.DPolicy.eq_20_heavy_traffic_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:16.699981+00:00
-- url     : https://prove2.me/theorems/47d8e5e8-2413-4220-93fa-f11070717d72
-- title:
--   Display (20), Online Appendix p. 6 — heavy-traffic limit lim_{λ→∞} W = L/V_c
-- statement:
--   Consider the $M/G_n/c/c$ loss queue with segment length $L > 0$, capacity $c \ge 1$ and speeds $V_1, \dots, V_c > 0$. As the arrival rate grows without bound, the mean travel time converges to the travel time of the segment at jam speed:
--   $$W_\infty = \lim_{\lambda \to \infty} W(\lambda) = \frac{L}{V_c}.$$
--
--   In heavy traffic the segment is almost always full, so every vehicle travels at the speed $V_c$ of a full segment. This limit turns the comparison of policies under heavy load into a comparison of jam speeds.
--
--   **Formalization Note** The limit is taken along $\lambda \to +\infty$ in $\mathbb R$ (`Filter.atTop`). Monotonicity of the speeds, a standing assumption of the paper, is not needed for this limit and is not assumed; the statement is therefore slightly more general than the page.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), proof of Proposition 1(a), display (20), Online Appendix p. 6

import Mathlib
import Definitions.Def_AVHighway_DPolicy_LossQueue

namespace AVHighway.DPolicy
theorem eq_20_heavy_traffic_limit (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) :
    Filter.Tendsto (meanTravelTime L V cap) Filter.atTop (nhds (L / V cap)) := by sorry
end AVHighway.DPolicy
