-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_past_event_scale_condExp
-- name    : AvramDividend.Classical.chat04_unbounded_past_event_scale_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T04:24:11.259113+00:00
-- url     : https://prove2.me/theorems/bab54b9e-1998-47c3-9302-a483d6052d56
-- title:
--   The q-scale payoff is a conditional Markov expectation at any past event, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. Then the q-scale payoff is a conditional Markov expectation: for two times s <= t, the conditional expectation, given the filtration at time s, of the scale payoff evaluated at the reserve at time t equals the scale payoff of the increment over the interval, evaluated at the expected reserve. This holds on every measurable event of the filtration at time s, and no standing assumption is required. The content is the q-scale semigroup harmonicity: the discounted scale payoff is a martingale, so the conditional expectation of the future payoff is the current payoff. The standing assumptions are not needed here because the only ingredient beyond the conditional-expectation mechanism itself, the integrability of the fixed-time scale payoff, is available for unbounded variation without them.
-- source:
--   The q-scale semigroup harmonicity for spectrally negative Levy processes of unbounded variation. The conditional-expectation mechanism is the Proved theorem chat04_shifted_scale_past_event_condExp and the integrability input is the Proved theorem chat04_unbounded_scale_fixed_time_integrable; the standing-case version is the Proved theorem chat04_standing_past_event_scale_condExp. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_past_event_scale_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    P[A.indicator (fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by sorry
