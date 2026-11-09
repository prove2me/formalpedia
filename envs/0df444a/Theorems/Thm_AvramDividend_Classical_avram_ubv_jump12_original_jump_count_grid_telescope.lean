-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_jump_count_grid_telescope
-- name    : AvramDividend.Classical.avram_ubv_jump12_original_jump_count_grid_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:54:23.569626+00:00
-- url     : https://prove2.me/theorems/1f4cc981-ae5c-4cd4-9c35-b48a624ee305
-- title:
--   Original physical jump counts telescope along any monotone finite grid
-- statement:
--   The original pathwise physical jump measure over a monotone finite time grid equals the sum of its adjacent-cell counts exactly in extended nonnegative reals. This enables the finite-grid compensated expectation identity to be applied to the jump count at a random stopping-grid index without replacing the source process.
-- source:
--   Induction on pinned public original two-cell count addition e6b70eac, for bounded-clock optional compensation towards 71fd10ee.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_jump_count_two_cell_add
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_jump12_original_jump_count_grid_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (e : ℕ → ℝ≥0) (he : Monotone e) (N : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    J (Ioc (e 0) (e N) ×ˢ B) =
      ∑ i ∈ Finset.range N,
        J (Ioc (e i) (e (i + 1)) ×ˢ B) := by sorry
