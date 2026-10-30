-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_reward_square_l2
-- name    : AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_square_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:59:56.915398+00:00
-- url     : https://prove2.me/theorems/594f6f84-f4c6-4631-8c8d-74817d78fb66
-- title:
--   Actual original-Lévy continuously killed grid square-reward second-moment bound
-- statement:
--   The actual continuous-history-killed q-scale reward has a square-integrable square and the same explicit bound as the accepted indicator-of-square L² theorem, by exact pointwise indicator-square commutation. This matches the uniform-second-moment expectation convergence theorem without assuming any unproved stopped semigroup or two-sided exit result.
-- source:
--   WS1A work/avram_root29_01_actual_killed_grid_reward_square_l2_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_l2

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_killed_grid_reward_square_l2
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
    Integrable (fun ω => (B.indicator (fun η =>
      Real.exp (-(q * (clock (K η) : ℝ))) *
        W (x + X.X (clock (K η)) η)) ω)^2) P ∧
    (∫ ω, (B.indicator (fun η =>
      Real.exp (-(q * (clock (K η) : ℝ))) *
        W (x + X.X (clock (K η)) η)) ω)^2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
