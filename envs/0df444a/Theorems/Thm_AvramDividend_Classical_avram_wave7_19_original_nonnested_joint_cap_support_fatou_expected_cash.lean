-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:46:30.244736+00:00
-- url     : https://prove2.me/theorems/3ad7a9d4-d8c3-43d1-ae7c-b454b3e0a495
-- title:
--   Original nonnested jointly measurable cap-plus-interior stopped Ito bounds imply complete finite-horizon expected ruin cash
-- statement:
--   For original spectrally negative Lévy dividends, let measurable random cap-support and arbitrary nonnested interior stopped windows jointly Borel in physical time and ω. If every genuine payment time (including zero, excluding strictly positive ruin) eventually lies in their union a.s., and liminf of the expected complete local discounted Stieltjes cash is bounded by budget, the exact full finite-horizon expected original ruin cash is bounded by budget. It imports the original joint random-support measurability lemma and source nonnested eventual-support pathwise Fatou inequality, then uses Mathlib lintegral_liminf_le on ω. No uniform integrability or unwarranted monotonicity of W7-18 stop windows, no cap-mass occupation-time assumption and no stronger canonical HJB condition.
-- source:
--   Source ruinTime/paymentTimes/dividendMeasure; accepted W7-19 joint random support Stieltjes measurability UUID 23624a57 and nonnested pathwise Fatou UUID 3fcca1a0; pinned Mathlib Fatou.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_joint_measurable_support_discounted_stieltjes_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_eventual_support_fatou_ruin_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (boundary : Ω → Set ℝ) (interior : ℕ → Ω → Set ℝ)
    (hBoundaryMeas : ∀ ω, MeasurableSet (boundary ω))
    (hInteriorMeas : ∀ n ω, MeasurableSet (interior n ω))
    (hJoint : ∀ n : ℕ,
      MeasurableSet {p : ℝ × Ω | p.1 ∈ boundary p.2 ∪ interior n p.2})
    (hEventual : ∀ᵐ ω ∂P,
      ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ∀ᶠ n : ℕ in Filter.atTop, t ∈ boundary ω ∪ interior n ω)
    (budget : ℝ≥0∞)
    (hBudgetLiminf : Filter.liminf (fun n : ℕ =>
      ∫⁻ ω, (∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P)
      Filter.atTop ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
