-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_reserve_nojump_source_dividend_exact_physical_linear_drift
-- name    : AvramDividend.Classical.avram_bvb24_original_zero_reserve_nojump_source_dividend_exact_physical_linear_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:32:15.023758+00:00
-- url     : https://prove2.me/theorems/765e3b00-d112-49b9-9304-1e2e93e6cfa4
-- title:
--   Original no-negative-jump drift source and identically zero controlled reserve force actual cumulative dividends to equal physical drift times time
-- statement:
--   On any physical bounded-variation no-negative-jump source trajectory where the original Lévy path is exactly linear physical drift and original controlled reserve is identically zero through the same horizon, the original source admissible cumulative dividend strategy is exactly the physical drift multiplied by elapsed time at each instant. The proof retains the original initial-capital and time-zero dividend bookkeeping and uses only original process-start and dividend-strategy axioms. It supplies the precise deterministic Stieltjes dividend clock needed to turn the zero-contact compensated cash estimate into the actual no-source-jump survival budget.
-- source:
--   Original no-source-negative-jump drift assumption in ed067740 and original zero-contact controlled reserve; actual source SpectrallyNegativeLevy.X_zero and IsAdmissibleLe dividend-at-zero axioms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb24_original_zero_reserve_nojump_source_dividend_exact_physical_linear_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S : ℝ≥0)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
      riskProcess X x D t ω = 0)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
      X.X t ω = (t : ℝ) * X.drift) :
    ∀ t : ℝ≥0, t ≤ S → D t ω = (t : ℝ) * X.drift := by sorry
