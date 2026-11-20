-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_all_k_m_bounded_by_horizon_and_ruin
-- name    : AvramDividend.Classical.avram_f6_original_rightmesh_all_k_m_bounded_by_horizon_and_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:54:27.885912+00:00
-- url     : https://prove2.me/theorems/f7dc07da-d286-423f-b877-2b0d0ae80141
-- title:
--   Original every-k physical rightmesh is bounded by the true finite horizon and ruin
-- statement:
--   For genuine original admissible dividends and clipped ruin clock τ=min(ruin,n), each actual physical rightmesh ρkm=min(τ,σk+1/(m+1)) is at most n and at most original ruinTime, for all k,m,ω. Uses the previously Proved original subordinate-clock bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_rightmesh_all_k_m_bounded_by_horizon_and_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ (k m : ℕ) (ω : Ω),
      let ρ : ℝ≥0 := min (τ ω)
        (σ k ω + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
      ρ ≤ (n : ℝ≥0) ∧
        (ρ : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
