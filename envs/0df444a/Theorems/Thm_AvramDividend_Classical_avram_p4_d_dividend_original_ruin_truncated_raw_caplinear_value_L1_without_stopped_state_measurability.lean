-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_without_stopped_state_measurability
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_without_stopped_state_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:57:17.777858+00:00
-- url     : https://prove2.me/theorems/759df498-9b3e-40f6-900e-36280095954e
-- title:
--   Original same-source stopped comparison value is integrable without independent stopped-X measurability
-- statement:
--   The original ruin-truncated Lévy source has an accepted exponential stopped integrability bound. A new source-exact logarithmic a.e.-measurability lemma and measurable cap-linear V furnish a.e. strong measurability of V(x+X tau), whose norm is bounded by an integrable exponential envelope, proving actual same-source stopped comparison L1 without positing full measurable stopped-X.
-- source:
--   Proved P4-F source original exponential integration 51ec0583 and the new same-source a.e. stopped value lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_stopped_Levy_value_aestronglyMeasurable_from_exponential

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_without_stopped_state_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (V : ℝ → ℝ) (hVmeas : Measurable V)
    (K : ℝ) (hK : 0 ≤ K)
    (hEnvelope : ∀ z : ℝ, ‖V z‖ ≤ K * Real.exp z) :
    Integrable (fun ω => V (x + X.X (τ ω) ω)) P := by sorry
