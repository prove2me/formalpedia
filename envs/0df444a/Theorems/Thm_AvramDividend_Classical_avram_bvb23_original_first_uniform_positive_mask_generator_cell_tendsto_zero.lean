-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_first_uniform_positive_mask_generator_cell_tendsto_zero
-- name    : AvramDividend.Classical.avram_bvb23_original_first_uniform_positive_mask_generator_cell_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:43:13.409536+00:00
-- url     : https://prove2.me/theorems/dd57a0d3-74b3-4d8f-9312-365035ec66ef
-- title:
--   Original first physical uniform grid positive-HJB generator contribution vanishes as its interval shrinks
-- statement:
--   For the original physical source process and exact prepayment left-limit reserve at the initial uniform grid point, the first open-interior masked HJB generator contribution converges to zero when the physical first grid width tends to zero. This remains valid even when the original initial right-payment makes the prepayment reserve positive. It uses the Proved discounted first-cell gain lemma directly and leaves all later physical grid cells to the zero-reserve prepayment bridge.
-- source:
--   Proved original physical first-cell discounted gain vanishes 3e722085; original BV-B22 strict-open generator mask at the initial source grid point.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva19_original_first_cell_discounted_gain_vanishes
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb23_original_first_uniform_positive_mask_generator_cell_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (q : ℝ) (ω : Ω)
    (u : ℕ → ℕ → ℝ≥0)
    (hzero : ∀ n, u n 0 = 0)
    (hmesh : Tendsto (fun n => (u n 1 : ℝ)) atTop (𝓝 (0 : ℝ))) :
    let U : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) t
    Tendsto (fun n =>
      Real.exp (-(q * (u n 0 : ℝ))) *
      (if (u n 0 : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < U (u n 0) ∧ ENNReal.ofReal (U (u n 0)) < C then
        X.generator w (U (u n 0)) - q * w (U (u n 0))
      else 0) *
      ((u n 1 : ℝ) - (u n 0 : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by sorry
