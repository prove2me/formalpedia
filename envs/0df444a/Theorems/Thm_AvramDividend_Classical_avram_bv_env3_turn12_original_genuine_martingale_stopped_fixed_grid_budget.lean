-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_genuine_martingale_stopped_fixed_grid_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_genuine_martingale_stopped_fixed_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:53:10.020988+00:00
-- url     : https://prove2.me/theorems/0c25e834-0a1e-4c07-9af8-6fab4f1e740f
-- title:
--   Original Lévy genuine martingale and HJB drift stopped over a fixed physical grid have nonpositive expected budget
-- statement:
--   For any genuine original martingale Y in the right-continuous Lévy filtration, the stopped original finite-grid martingale increments plus integrable pointwise nonpositive drift have a finite integrable nonpositive expected signed source. This specializes the fully proved original stopped fixed-grid conditional-zero reduction with a concrete martingale conditional-mean-zero proof.
-- source:
--   Accepted fixed physical grid stopped source 67302ed2 and original martingale increment condexp zero b065494f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_genuine_martingale_stopped_fixed_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (B : ℕ → Ω → ℝ) (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
        (if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) + B i ω else 0)
      ∂P) ≤ 0 := by sorry
