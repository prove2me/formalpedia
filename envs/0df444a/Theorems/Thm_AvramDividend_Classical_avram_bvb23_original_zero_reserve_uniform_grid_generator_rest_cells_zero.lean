-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_zero_reserve_uniform_grid_generator_rest_cells_zero
-- name    : AvramDividend.Classical.avram_bvb23_original_zero_reserve_uniform_grid_generator_rest_cells_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:42:29.817291+00:00
-- url     : https://prove2.me/theorems/143dbe1c-37fc-4df2-95d9-3d4a1d2d9f73
-- title:
--   Original finite BV uniform-grid positive-interior generator sum reduces exactly to the first physical cell on zero-reserve paths
-- statement:
--   For the exact original spectrally negative Levy controlled source and physical uniform-grid prepayment left limits, assume every grid point lies in the stopped horizon, the original prepayment left-limit equals the actual postpayment controlled reserve at grid endpoints, and the original controlled reserve is zero throughout the horizon. Then all strictly positive-interior HJB generator terms after the first grid point vanish identically, so the original finite generator sum equals its initial cell summand. This isolates the genuinely delicate initial right-payment contact rather than assuming the initial prepayment reserve is zero.
-- source:
--   Original ed067740 survival target, original hPre relation, Proved physical grid horizon bound 7a37b233, Finset.sum_eq_single.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_zero_reserve_uniform_grid_generator_rest_cells_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω) (S : ℝ≥0)
    (hBound : ∀ i, i ≤ n + 1 → u n i ≤ S)
    (hPre : ∀ i : ℕ,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)
    (hZero : ∀ t : ℝ≥0, t ≤ S → riskProcess X x D t ω = 0) :
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let G : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    (∑ i ∈ Finset.range (n + 1), G i) = G 0 := by sorry
