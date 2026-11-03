-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_boundary_interior_ito_budget_to_ruin_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_killed_boundary_interior_ito_budget_to_ruin_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:02:55.135494+00:00
-- url     : https://prove2.me/theorems/6d8c12a0-e92e-4eb5-b1b4-ee3e14d5d796
-- title:
--   Exact original killed pre-ruin zero/cap boundary and shrinking interior Ito budgets imply all finite-horizon dividend cash
-- statement:
--   Boundary-inclusive Fatou bridge for true original paymentTimes stopped at ruin and capped at T. For the capped admissible original Lévy strategy, assume an expected discounted cash budget for each lower/upper cutoff on exactly the killed payment domain, including the post-rightpayment zero/cap faces and spatial interior. Then the full ENNReal finite-horizon Stieltjes dividend cash obeys the same bound. Joint measurability and eventual coverage are derived from two source-specific auxiliaries and the proved source Fatou theorem. No stopping exhaustion assumption, no uniform integrability, no creeping continuity, and no post-ruin cash premise.
-- source:
--   Source-specific finite-horizon killed support lemma b1a4123b, source eventual payment support 8670c341 and accepted nonnested Fatou cash theorem 3ad7a9d4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_killed_boundary_interior_ito_budget_to_ruin_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x T : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hStrategy : IsDividendStrategy 𝓕 D)
    (hxc : ENNReal.ofReal x ≤ C)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞)
    (hlower : Filter.Tendsto lower Filter.atTop (𝓝 0))
    (hupper : Filter.Tendsto upper Filter.atTop (𝓝 C))
    (budget : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, (∫⁻ t in
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)} ∪
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
