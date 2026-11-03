-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_cap_retaining_spatial_support_expected_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_cap_retaining_spatial_support_expected_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:14:59.404008+00:00
-- url     : https://prove2.me/theorems/92c96663-e1fb-40b0-a34e-087e11142542
-- title:
--   Original expected ruin cash bound from interior cutoffs retaining measurable cap-supported payments
-- statement:
--   This is the missing original-process cap-preserving monotone spatial localisation expectation bridge. A measurable increasing family of interior-time supports may cover all strict pre-ruin paying times only after adjoining an explicit boundary support containing cap-paid dividends. The exact source set cover is an almost-sure hypothesis, and every corrected local cash includes the full boundary-supported dividendMeasure contribution. By the source pathwise monotone-support iSup lemma, full cash≤sup corrected local cash. The previously Proved W7-19 original spatial expectation MCT transfers uniform corrected stopped cash bounds to full finite-horizon expected cash. No UI, no cap occupation-time claim, no right-continuity at ruin and no added canonical generator hypotheses. W7-18 must establish the support cover and measurable local cash; W7-08/W7-05/06/07 must establish the local source Ito budgets.
-- source:
--   W7-19 source exact monotone boundary support cash iSup helper and Proved original spatial MCT f5df271c. Completes cap-supported Stieltjes boundary correction without W7-03 real/ENNReal measure conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_cap_retaining_spatial_support_expected_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (boundary : Ω → Set ℝ) (interior : ℕ → Ω → Set ℝ)
    (hBoundaryMeas : ∀ ω, MeasurableSet (boundary ω))
    (hInteriorMeas : ∀ n ω, MeasurableSet (interior n ω))
    (hInteriorMon : ∀ ω, Monotone (fun n => interior n ω))
    (hCover : ∀ᵐ ω ∂P,
      paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
        ⋃ n : ℕ, boundary ω ∪ interior n ω)
    (hLocalCashMeas : ∀ n, Measurable (fun ω =>
      ∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (budget : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, (∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
