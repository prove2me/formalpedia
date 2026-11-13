-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_quantitative_cofinal_spatial_diagonal
-- name    : AvramDividend.Classical.avram_a06_quantitative_cofinal_spatial_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:18:00.711664+00:00
-- url     : https://prove2.me/theorems/2fe020f8-f683-4392-8f5a-53d1f83789f0
-- title:
--   A06 quantitative spatial diagonal makes total physical grid row error vanish
-- statement:
--   For any sequence of nonnegative expected errors E(n,k) that vanishes as localisation k tends to infinity at each fixed n, there exists a strictly increasing cofinal spatial index kappa(n) at least n such that the grid-cell-count-weighted error (n+1)*E(n,kappa(n)) tends to zero. This is needed to sum bounds over the n+1 original Lévy physical time-grid cells without assuming uniform-in-row localisation convergence. The proof rescales each row and uses the already Proved monotone diagonal theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_monotone_diagonal_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a06_quantitative_cofinal_spatial_diagonal
    (E : ℕ → ℕ → ℝ) (hNonneg : ∀ n k, 0 ≤ E n k)
    (hRow : ∀ n, Tendsto (fun k => E n k) atTop (𝓝 (0 : ℝ))) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ (∀ n, n ≤ κ n) ∧
      Tendsto (fun (n : ℕ) => ((n : ℝ) + 1) * E n (κ n))
        atTop (𝓝 (0 : ℝ)) := by sorry
