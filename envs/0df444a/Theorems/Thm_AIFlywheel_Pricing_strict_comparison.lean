-- Prove2me | Theorems.Thm_AIFlywheel_Pricing_strict_comparison
-- name    : AIFlywheel.Pricing.strict_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:59.471162+00:00
-- url     : https://prove2.me/theorems/46021fb4-41b7-49e6-9040-aa7fa31d52d8
-- title:
--   Proof of Theorem 1: interior optima differ under strict monotonicity
-- statement:
--   Suppose the optimal contract quantity $\delta^*$ and the first-best quantity $\delta^{FB}$ are both interior to $(0,\nu)$. When the data impact $\rho$ is strictly increasing or strictly decreasing on the feasible dataset interval, the two optimal quantities cannot coincide:
--   $$
--   \delta^*\ne\delta^{FB}.
--   $$
--   This is the strictness statement invoked in the proof of Theorem 1 after its weak comparison.
--
--   **Formalization Note.** The interior condition expresses the paper's standing price assumption; the two derivatives used in the source's first-order comparison are available from the model's differentiability assumptions.
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, p. 29 (PDF 30), proof of Theorem 1, sentence after (23); interior prices assumed p. 11 (PDF 12).

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

namespace AIFlywheel.Pricing

/-- The unequal-optima step in the proof of Theorem 1, p. 29. -/
theorem strict_comparison (P : Params) (hP : P.Standing)
    (s : Plan) (hs : IsOptimal P s)
    (fh fl : ℝ) (hf : IsFBOptimal P fh fl)
    (hint : s.δ1l ∈ Set.Ioo 0 P.ν ∧ fl ∈ Set.Ioo 0 P.ν) :
    (StrictMonoOn (dataImpact P) (Set.Icc P.dmin P.dmax) ∨
      StrictAntiOn (dataImpact P) (Set.Icc P.dmin P.dmax)) →
      s.δ1l ≠ fl := by sorry

end AIFlywheel.Pricing
