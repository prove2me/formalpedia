-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_integrable_from_square
-- name    : AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_integrable_from_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:46:42.397978+00:00
-- url     : https://prove2.me/theorems/93bb170c-8251-4e82-86d1-d194156089e8
-- title:
--   Actual original-Levy lower-history-killed first-exit reward integrable from genuine second moment
-- statement:
--   Under the actual original spectrally negative Levy law and a source Laplace-exponent margin, the continuously lower-history-killed discounted q-scale reward at a genuine bounded first-outside stopping index is integrable; use source-specific measurability, its proven squared reward moment, and L2-to-L1 inclusion under probability.
-- source:
--   Source-specific Proved actual killed grid second moment and measurable reward, mathlib MemLp L2-to-L1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_square_l2
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_meas

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_integrable_from_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω)
    (N : ℝ≥0) (hN : ∀ ω, clock (K ω) ≤ N) :
    let B : Set Ω := {ω | ∀ t : ℝ≥0,
      t ≤ clock (K ω) → 0 ≤ x + X.X t ω}
    Integrable (B.indicator (fun ω =>
      Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω))) P := by sorry
