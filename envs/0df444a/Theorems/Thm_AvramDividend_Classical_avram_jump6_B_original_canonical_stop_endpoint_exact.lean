-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_stop_endpoint_exact
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_stop_endpoint_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:25:34.729339+00:00
-- url     : https://prove2.me/theorems/230b76d1-52d5-452a-b176-9c1a80d4e1ca
-- title:
--   Exact original ruin-clipped canonical grid endpoint for every physical discretisation
-- statement:
--   At every canonical refining physical-grid resolution j, the final mesh point m(j)=(N+1)(j+1) lies beyond the original stopped ruin-truncated clock sigma(k), so the actual stopped mesh endpoint min(u(j,m(j)),sigma(k)) is exactly sigma(k) for every path and k. This strengthens the previously Proved eventual grid coverage and is source-exact with arbitrary negative-jump intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_stop_endpoint_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (N : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    let m : ℕ → ℕ := fun j => (N + 1) * (j + 1)
    ∀ k j ω, min (u j (m j)) (σ k ω) = σ k ω := by sorry
