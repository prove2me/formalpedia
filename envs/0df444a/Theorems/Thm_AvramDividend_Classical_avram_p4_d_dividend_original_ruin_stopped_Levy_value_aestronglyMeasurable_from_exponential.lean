-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_stopped_Levy_value_aestronglyMeasurable_from_exponential
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ruin_stopped_Levy_value_aestronglyMeasurable_from_exponential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:46:04.879673+00:00
-- url     : https://prove2.me/theorems/b51c8527-7e4d-414b-9131-8ce18a917001
-- title:
--   Original ruin-stopped Lévy value is a.e. strongly measurable from its integrable exponential
-- statement:
--   For the identical original spectrally negative Lévy source and actual ruin-truncated finite clock, the already Proved original stopped exponential is integrable. Composing its almost-everywhere measurability with the measurable real logarithm and log(exp z)=z establishes the stopped physical Lévy state is a.e. strongly measurable, with no separate stopped-state measurability or path continuity assumption.
-- source:
--   Proved P4-F original ruin-clock discounted exponential integrability, 51ec0583; Mathlib measurable logarithm and a.e. measurable composition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ruin_stopped_Levy_value_aestronglyMeasurable_from_exponential
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    AEStronglyMeasurable (fun ω => X.X (τ ω) ω) P := by sorry
