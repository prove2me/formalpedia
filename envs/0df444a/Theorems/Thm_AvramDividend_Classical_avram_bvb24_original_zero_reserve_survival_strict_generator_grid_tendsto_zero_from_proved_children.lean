-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_reserve_survival_strict_generator_grid_tendsto_zero_from_proved_children
-- name    : AvramDividend.Classical.avram_bvb24_original_zero_reserve_survival_strict_generator_grid_tendsto_zero_from_proved_children
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:37:03.531206+00:00
-- url     : https://prove2.me/theorems/2b1be52d-9fcb-4104-b023-9be8491ee43e
-- title:
--   Entire original strictly positive-interior HJB generator sum tends to zero on surviving nojump zero-controlled-reserve source paths
-- statement:
--   For the original physical uniform finite grid with initial time zero and vanishing first mesh width, under the source prepayment-left-limit vs controlled postpayment relation and a controlled reserve identically zero on the physical horizon, the complete strictly positive-interior HJB generator sum converges to zero. Every noninitial sampled term is identically zero, and the remaining possible positive initial right-payment contact term vanishes as its first cell shrinks. This provides the original G_n component of the everywhere-zero-contact survival branch and avoids silently identifying initial prepayment reserve with postpayment reserve.
-- source:
--   Both exact prerequisites now authoritative Proved: 143dbe1c and dd57a0d3; earlier publication submitted while prerequisites were still Open and never indexed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_zero_reserve_uniform_grid_generator_rest_cells_zero
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_first_uniform_positive_mask_generator_cell_tendsto_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb24_original_zero_reserve_survival_strict_generator_grid_tendsto_zero_from_proved_children
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℕ → ℝ≥0) (ω : Ω) (S : ℝ≥0)
    (hzero : ∀ n, u n 0 = 0)
    (hBound : ∀ n i, i ≤ n + 1 → u n i ≤ S)
    (hmesh : Tendsto (fun n => (u n 1 : ℝ))
      atTop (𝓝 (0 : ℝ)))
    (hPre : ∀ n i : ℕ,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
      riskProcess X x D t ω = 0) :
    let Z : ℕ → ℕ → ℝ := fun n i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let G : ℕ → ℕ → ℝ := fun n i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z n i ∧ ENNReal.ofReal (Z n i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z n i) - q * w (Z n i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    Tendsto (fun n => ∑ i ∈ Finset.range (n + 1), G n i)
      atTop (𝓝 (0 : ℝ)) := by sorry
