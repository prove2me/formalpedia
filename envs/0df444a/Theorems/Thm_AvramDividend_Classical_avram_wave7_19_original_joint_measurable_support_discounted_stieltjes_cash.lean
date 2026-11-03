-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:17:37.130817+00:00
-- url     : https://prove2.me/theorems/23624a57-b7c7-4b3e-8e14-d3590c1e9f65
-- title:
--   Jointly measurable original random payment-time supports have measurable discounted Stieltjes cash
-- statement:
--   For the actual original dividendMeasure of a left-continuous admissible source dividend strategy, any jointly measurable random support S⊆ℝ×Ω has a measurable ENNReal discounted Stieltjes reward on its ω-section. The proof uses the Proved global s-finite source dividendMeasure kernel and measurable_random_indicator_lintegral, with no real/ENNReal measure conversion. This permits W7-18's jointly measurable boundary union interior support to discharge the hLocalCashMeas hypothesis of W7-19's original cap-retaining spatial expectation bridge. It retains every Stieltjes component, including singular cap-reflection payouts and right-payment atoms, and does not assume source path continuity at ruin.
-- source:
--   Original dividendMeasure global s-finite kernel; Proved measurable_random_indicator_lintegral; direct original source paid cash on general W7-18 joint cap/interior time support. No W7-03 signed conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (S : Set (ℝ × Ω)) (hS : MeasurableSet S) (q : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in {t : ℝ | (t, ω) ∈ S},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
