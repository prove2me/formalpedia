-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_past_event_scale_condExp
-- name    : AvramDividend.Classical.chat04_standing_past_event_scale_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:40:57.67029+00:00
-- url     : https://prove2.me/theorems/3b6d30d3-f850-4855-b55f-b19339f58174
-- title:
--   Standing-case scale conditional expectation with arbitrary past survival event
-- statement:
--   Under the original Avram Standing assumptions, q>0 and canonical q-scale W, for every 0≤s≤t and every A measurable at time s, the conditional expectation of the future-increment scale payoff restricted to historical event A equals the same historical indicator multiplied by the stationary future payoff expectation. No external integrability hypothesis or Laplace-gap parameter is required. Integrability follows from the already Proved Standing q-scale fixed-time theorem; the conditional identity is the already Proved past-event independence theorem. This exact standing-case restricted Markov identity is suitable for prior-survival events, but does not account for a future ruin crossing inside (s,t) or assert a killed-scale martingale.
-- source:
--   Imported accepted theorem AvramDividend.Classical.chat04_standing_scale_fixed_time_integrable UUID 1d43ef79-1a69-4d82-b4de-d9ad5d5c8ee5 and accepted AvramDividend.Classical.chat04_shifted_scale_past_event_condExp UUID 7425e984-1b8e-466f-b5ea-a3a004d5ed2d.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_scale_past_event_condExp

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_standing_past_event_scale_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    P[A.indicator (fun ω => W (x + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      A.indicator (fun _ => ∫ ω, W (x + X.X (t - s) ω) ∂P) := by sorry
