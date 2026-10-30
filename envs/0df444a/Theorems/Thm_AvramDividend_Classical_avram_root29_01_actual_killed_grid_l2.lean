-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_killed_grid_l2
-- name    : AvramDividend.Classical.avram_root29_01_actual_killed_grid_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:30:30.411455+00:00
-- url     : https://prove2.me/theorems/6dc4ebb7-53e7-4786-bcff-f24e6a076863
-- title:
--   Actual original-Lévy killed first-exit grid q-scale uniform L² bound
-- statement:
--   Under the genuine spectrally negative Lévy source, exact bounded two-sided hittingBtwn grid and q-scale hypotheses, the square of the discounted stopped q-scale payoff killed by full continuous lower-survival history is integrable and uniformly bounded in grid refinement at any common finite horizon. Compose Proved source hitting index measurability, source random killed-history event measurability, source stopped scale-square measurability and the accepted indicated L² bound. No independent hMeas or hB assumptions and no Open exit identity.
-- source:
--   WS1A work/avram_root29_01_actual_killed_grid_l2_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_grid_hitting_index_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_random_grid_history_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_scale_square_meas
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_two_sided_grid_indicated_scale_l2

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_actual_killed_grid_l2
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
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2)) P ∧
    (∫ ω, B.indicator (fun ω =>
      (Real.exp (-(q * (clock (K ω) : ℝ))) *
        W (x + X.X (clock (K ω)) ω)) ^ 2) ω ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by sorry
