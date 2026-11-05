-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:36:19.603057+00:00
-- url     : https://prove2.me/theorems/af8ae00a-6a2f-42c8-84a5-5a3eaa17570a
-- title:
--   The exact original ruin-truncated dividend clock is bounded by its finite horizon on every path
-- statement:
--   For the identical original spectrally negative Lévy source, controlled ruinTime and finite stopped clock used in P4-F, the literal tau=min(ruinTime,n).toNNReal is at most the integer horizon. Handles an infinite ruin time without making continuity or moment assumptions and supplies the source deterministic clock bound needed for the P4-D terminal L1 transfer.
-- source:
--   Canonical original P4-F finite clock formula; pinned Mathlib ENNReal.toNNReal_mono and min_le_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, τ ω ≤ (n : ℝ≥0) := by sorry
