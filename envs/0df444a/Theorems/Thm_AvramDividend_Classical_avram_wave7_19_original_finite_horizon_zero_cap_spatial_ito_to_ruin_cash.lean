-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_finite_horizon_zero_cap_spatial_ito_to_ruin_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_finite_horizon_zero_cap_spatial_ito_to_ruin_cash
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T21:35:32.325663+00:00
-- url     : https://prove2.me/theorems/97c8d8af-e97d-43d1-b3a9-17d7072630c5
-- title:
--   Finite-horizon original zero/cap boundary plus shrinking interior stopped Ito cash bounds yield the complete ruin payment inequality
-- statement:
--   The exact source finite-horizon W7-19 cash bridge. Given the original capped-admissible strategy, an initial cap, deterministic lower and upper spatial cutoffs tending to zero and C, and finite-horizon local stopped Ito cash budgets on the explicit zero/cap boundary plus interior regions (both intersect Iic T), the complete finite-horizon discounted ENNReal original Stieltjes ruin cash is bounded by budget. The real-time eventual-support and joint measurability are derived from source original-process lemmas and Fatou; no uniform integrability, ruin continuity or monotone stop clocks are assumed. Boundary right dividends and cap reflection mass are fully included. The extra hStrategy argument is logically already contained in IsAdmissibleLe.
-- source:
--   W7-19 accepted source nonnested Fatou expected cash UUID 3ad7a9d4, source real spatial coverage 8670c341 and joint Borel support 0b1a5931; finite deterministic horizon restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_finite_horizon_zero_cap_spatial_ito_to_ruin_cash
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
      (∫⁻ ω, (∫⁻ t in {t : ℝ | (0 ≤ t ∧ (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨ ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)) ∧ t ≤ T} ∪ {t : ℝ | (0 ≤ t ∧ lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧ ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n) ∧ t ≤ T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
