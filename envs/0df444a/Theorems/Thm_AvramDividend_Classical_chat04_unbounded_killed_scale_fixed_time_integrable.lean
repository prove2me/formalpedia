-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_fixed_time_integrable
-- name    : AvramDividend.Classical.chat04_unbounded_killed_scale_fixed_time_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:59:23.826526+00:00
-- url     : https://prove2.me/theorems/4d2ca4b6-b8a5-46dc-85a6-02ef046e6339
-- title:
--   Canonical downward-killed q-scale payoff is integrable without Standing or an auxiliary observation schedule
-- statement:
--   For any spectrally negative Lévy process of unbounded variation and q>0, the fixed-time discounted q-scale payoff restricted to survival above ruin throughout the continuous path history is Bochner integrable. No Standing assumptions and no extra mesh enumeration are required: instantiate the already proved grid-schedule-parametrised killed-payoff integrability lemma using the explicit Nat.unpair Cantor-pairing schedule, whose complete reciprocal-natural grid coverage is already proved. This is the unconditional fixed-time integrability precondition of the correct killed q-scale martingale.

import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_fixed_time_integrable_of_cover
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_scale_fixed_time_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    Integrable (({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) P := by sorry
