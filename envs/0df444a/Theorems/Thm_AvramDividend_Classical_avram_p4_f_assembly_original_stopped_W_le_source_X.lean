-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_W_le_source_X
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_stopped_W_le_source_X
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:06:55.38982+00:00
-- url     : https://prove2.me/theorems/ddf76c68-bd4e-4880-91dd-faa662ff2eed
-- title:
--   Actual original stopped dividend-controlled terminal reserve is bounded by raw Lévy capital
-- statement:
--   For every admissible original nondecreasing dividend control and arbitrary finite or infinite cap, the genuine postpayment-or-ruin stopped reserve W never exceeds x+Xτ. The postpayment case uses rightLimit D≥D≥0; the ruin case uses riskProcess=x+X-D and D≥0. This reduction permits future infinite-cap integrability bounds via original spectrally negative Lévy positive exponential moments instead of a false bounded cap.
-- source:
--   Accepted dividendStrategy_path_nonneg 716ba871 and dividendStrategy_le_rightLimit 953f0e91, original riskProcess and canonical W definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_stopped_W_le_source_X
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω ≤ x + X.X (τ ω) ω := by sorry
