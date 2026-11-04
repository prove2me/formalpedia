-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_min_ruin_survival_branch_iff_horizon_before_ruin
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_min_ruin_survival_branch_iff_horizon_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:50:50.271426+00:00
-- url     : https://prove2.me/theorems/99ca2614-ddb8-4f19-8068-21efcd95b73c
-- title:
--   At the exact original clipped clock, strict survival is equivalent to the fixed horizon strictly before ruin
-- statement:
--   For the original extended-real ruin time and the P4-F source τ=(min ruinTime n).toNNReal, strict terminal survival τ<ruin holds exactly when the deterministic finite horizon n<ruin. The equality case ruin=n belongs to ruin, not survival. This source-backed lemma resolves the strict endpoint convention for the terminal W branch (the special τ=0 disjunct remains separately present in P4-F).
-- source:
--   Exact P4-F hτeq; pinned Mathlib ENNReal.coe_toNNReal and linear-order min_lt_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict source terminal survival at the finite clipped clock is exactly horizon-before-ruin. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_min_ruin_survival_branch_iff_horizon_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) < ruinTime X x D ω ↔
      (n : ℝ≥0∞) < ruinTime X x D ω := by sorry
