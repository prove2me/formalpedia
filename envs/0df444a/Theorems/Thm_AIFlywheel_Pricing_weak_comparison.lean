-- Prove2me | Theorems.Thm_AIFlywheel_Pricing_weak_comparison
-- name    : AIFlywheel.Pricing.weak_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:56.050992+00:00
-- url     : https://prove2.me/theorems/d3ac45df-710d-4301-b63a-bace37f5b7ec
-- title:
--   Proof of Theorem 1: weak data comparison
-- statement:
--   Let $\delta^*$ be the low-accuracy data quantity of any optimal feasible contract and $\delta^{FB}$ the corresponding first-best optimal quantity. The comparison in the proof of Theorem 1 gives
--   $$
--   \rho\text{ strictly decreasing}\ \Longrightarrow\ \delta^*\le\delta^{FB},
--   \qquad
--   \rho\text{ strictly increasing}\ \Longrightarrow\ \delta^*\ge\delta^{FB}.
--   $$
--   Monotonicity is on the feasible dataset interval $[d_{\min},d_{\max}]$. These weak inequalities isolate the global optimum comparison before the interior strictness step.
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, p. 29 (PDF 30), proof of Theorem 1, equations (22)–(23) and the final sentence of the proof.

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

namespace AIFlywheel.Pricing

/-- The weak comparison in the proof of Theorem 1, p. 29, from (22)–(23). -/
theorem weak_comparison (P : Params) (hP : P.Standing)
    (s : Plan) (hs : IsOptimal P s)
    (fh fl : ℝ) (hf : IsFBOptimal P fh fl) :
    (StrictAntiOn (dataImpact P) (Set.Icc P.dmin P.dmax) → s.δ1l ≤ fl) ∧
    (StrictMonoOn (dataImpact P) (Set.Icc P.dmin P.dmax) → fl ≤ s.δ1l) := by sorry

end AIFlywheel.Pricing
