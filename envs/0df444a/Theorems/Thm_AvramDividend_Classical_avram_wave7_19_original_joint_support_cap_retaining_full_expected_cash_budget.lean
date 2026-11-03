-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_joint_support_cap_retaining_full_expected_cash_budget
-- name    : AvramDividend.Classical.avram_wave7_19_original_joint_support_cap_retaining_full_expected_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:19:11.745084+00:00
-- url     : https://prove2.me/theorems/d9a3f25d-0aa8-4f01-9d1a-636e64ef22bf
-- title:
--   Source joint cap and interior support Ito budgets imply complete expected ruin cash without an extra cash-measurability premise
-- statement:
--   Final W7-19 corrected interface from W7-18's actual measurable cap support and nested interior reserve windows to the full original finite-horizon ENNReal dividend bound. The source measurable random support kernel theorem derives every local cash measurability premise from joint support measurability; the source cap-retaining spatial MCT transfers the uniform stopped source cash budgets. All cap-paid continuous or singular Stieltjes mass remains explicitly in the stopped cash; only source set coverage and the stopped Ito budgets remain to be discharged by W7-18 and W7-08, respectively. No new canonical assumptions or W7-03 real/ENNReal conversion.
-- source:
--   Composition of two source-specific W7-19 cap retention and joint support measurability bridges, reducing W7-18's time-support evidence and W7-08 stopped Ito budgets directly to the original expectation target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_joint_support_cap_retaining_full_expected_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (boundary : Ω → Set ℝ) (interior : ℕ → Ω → Set ℝ)
    (hBoundaryMeas : ∀ ω, MeasurableSet (boundary ω))
    (hInteriorMeas : ∀ n ω, MeasurableSet (interior n ω))
    (hJoint : ∀ n : ℕ,
      MeasurableSet {p : ℝ × Ω | p.1 ∈ boundary p.2 ∪ interior n p.2})
    (hInteriorMon : ∀ ω, Monotone (fun n => interior n ω))
    (hCover : ∀ᵐ ω ∂P,
      paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
        ⋃ n : ℕ, boundary ω ∪ interior n ω)
    (budget : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, (∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
