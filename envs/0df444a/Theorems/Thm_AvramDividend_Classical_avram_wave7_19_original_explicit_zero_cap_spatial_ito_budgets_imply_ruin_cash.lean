-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_explicit_zero_cap_spatial_ito_budgets_imply_ruin_cash
-- name    : AvramDividend.Classical.avram_wave7_19_original_explicit_zero_cap_spatial_ito_budgets_imply_ruin_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:31:29.330773+00:00
-- url     : https://prove2.me/theorems/ae82ceb5-ece8-4794-80a9-ce4f26c01ef3
-- title:
--   Original stopped Ito budgets on explicit zero/cap payment boundary and shrinking interior bands imply complete finite-horizon ruin cash
-- statement:
--   Concrete W7-19 bridge with the exact original risk process after right dividend payment, source real Stieltjes dividendMeasure and paymentTimes. Assume only original capped admissibility, initial cap, cutoffs tending to zero and C, and the local expected stopped Ito cash budgets INCLUDING zero/cap supported dividend mass. Then the full ruin-before-horizon ENNReal expected dividend cash is bounded by budget. Joint Borel support and eventual spatial coverage are discharged from separate original source lemmas; the already Proved nonnested Fatou expectation lemma finishes without uniform integrability. Additional hStrategy merely exposes the IsAdmissibleLe underlying dividend strategy to Lean and is derivable from canonical hD; no new stochastic/HJB condition.
-- source:
--   Accepted W7-19 nonnested joint-support Fatou theorem UUID 3ad7a9d4; original real-payment eventual spatial coverage UUID 8670c341; real jointly measurable support UUID 0b1a5931.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_explicit_zero_cap_spatial_ito_budgets_imply_ruin_cash
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
        {t : ℝ | 0 ≤ t ∧ (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨ ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)} ∪ {t : ℝ | 0 ≤ t ∧ lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧ ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by sorry
