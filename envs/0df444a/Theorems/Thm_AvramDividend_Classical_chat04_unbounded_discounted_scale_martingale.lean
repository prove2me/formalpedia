-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_discounted_scale_martingale
-- name    : AvramDividend.Classical.chat04_unbounded_discounted_scale_martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T04:58:02.527035+00:00
-- url     : https://prove2.me/theorems/d38b09a0-3b25-4dba-99f8-7fb3a25eb95b
-- title:
--   The discounted q-scale payoff is a martingale, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. Then for every starting point x the discounted q-scale payoff, t |-> exp(-q t) W(x + X_t), is a martingale with respect to the natural filtration of the process. This is the q-scale semigroup harmonicity in its martingale form, the Doob h-transform of the scale function: the q-scale function is the density of the killed process, and the discounted payoff of that density is a martingale. It is the hypothesis that the two-sided exit identity needs, since optional stopping at the first exit of an interval then identifies the expected stopped payoff with the initial payoff. No standing assumption is required: the integrability of the fixed-time payoff, which the martingale property needs, is available for unbounded variation without the standing integrability of the process increment.
-- source:
--   The q-scale martingale of a spectrally negative Levy process, the form of the semigroup harmonicity in which the discounted q-scale payoff is a martingale; it is the hypothesis of the two-sided exit identity of Avram, Palmowski and Pistorius (2007), equation (3.6). The semigroup statement is the Proved theorem chat04_unbounded_past_event_scale_condExp and the integrability it needs is the Proved theorem chat04_unbounded_scale_fixed_time_integrable. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_discounted_scale_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) :
    Martingale (fun t : ℝ≥0 => fun ω =>
      Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) 𝓕 P := by sorry
