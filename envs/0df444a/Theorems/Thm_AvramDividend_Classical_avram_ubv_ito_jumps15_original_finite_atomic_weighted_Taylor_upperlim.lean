-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps15_original_finite_atomic_weighted_Taylor_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps15_original_finite_atomic_weighted_Taylor_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:46:29.620267+00:00
-- url     : https://prove2.me/theorems/a7bee22b-26af-4b63-b526-c86333bd658e
-- title:
--   Original stopped negative jump Taylor remainder upperlim for finite nonnegative atomic Levy intensity
-- statement:
--   For a finite set of strictly negative marks carrying arbitrary nonnegative intensity weights, the genuine original capped C2 value's Taylor residual weighted jump sum admits a common one-sided upper mesh bound. The permitted error is delta times the total atomic intensity; no assumption excludes an atom precisely crossing to zero. This is the finite-atomic case, leaving infinite-activity measure integration separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps15_original_finite_atomic_weighted_Taylor_upperlim
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y))
    (a : ℝ → ℝ) (ha : ∀ z : ℝ, 0 ≤ a z) :
    let R : ℝ → ℝ → ℝ := fun x z =>
      w (x + z) - w x -
        (if -1 < z then z * deriv w x else 0)
    ∀ S : Finset ℝ, (∀ z ∈ S, z < 0) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        S.sum (fun z => a z * R (u n) z) ≤
          S.sum (fun z => a z * R y z) + δ * S.sum a := by sorry
