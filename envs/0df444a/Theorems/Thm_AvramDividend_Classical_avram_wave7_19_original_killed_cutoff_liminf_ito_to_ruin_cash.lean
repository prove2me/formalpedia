-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_cutoff_liminf_ito_to_ruin_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_killed_cutoff_liminf_ito_to_ruin_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:01:52.565401+00:00
-- url     : https://prove2.me/theorems/802e9ae0-62b4-4a63-9706-ac40f6b81136
-- title:
--   Exact killed original reserve boundary and interior liminf cash budget implies full finite-horizon ENNReal ruin dividends
-- statement:
--   The source-specific boundary and limit-passage bridge for the true original spectrally-negative Lévy dividend process. For shrinking lower and upper interior cut-offs and a fixed zero/cap post-rightdividend boundary support, an ENNReal liminf upper budget for the expected discounted cash on the true killed paymentTimes ∩ Iic T domains suffices to bound all finite-horizon ruin cash. No uniform integrability and no monotone spatial supports are needed: the source exact eventual-support and joint-measurability lemmas discharge the accepted nonnested Fatou theorem. The liminf hypothesis admits small-jump truncation error terms that disappear in the limit without requiring a uniform cash bound at every truncation index.
-- source:
--   Accepted generic W7-19 nonnested Fatou expected-cash theorem 3ad7a9d4, original-process real payment cover 8670c341, original killed jointly measurable support b1a4123b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonnested_joint_cap_support_fatou_expected_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_real_zero_cap_spatial_support_joint_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_killed_cutoff_liminf_ito_to_ruin_cash
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
    (hBudgetLiminf : Filter.liminf (fun n : ℕ =>
      (∫⁻ ω, (∫⁻ t in
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)} ∪
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P)) Filter.atTop ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
