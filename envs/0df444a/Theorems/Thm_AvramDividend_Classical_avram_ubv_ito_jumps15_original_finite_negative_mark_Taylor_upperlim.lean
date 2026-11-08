-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps15_original_finite_negative_mark_Taylor_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps15_original_finite_negative_mark_Taylor_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:38:36.834578+00:00
-- url     : https://prove2.me/theorems/a8344989-ea77-4ba2-8f38-6f1a83e5da8c
-- title:
--   Finite original negative Lévy marks retain one-sided C2 Taylor upper mesh limit at simultaneous zero contact
-- statement:
--   Given the original capped C2 value with nonnegative boundary value and its zero extension, the actual Taylor remainders for every finite set of strictly negative Lévy marks have a common one-sided upper mesh limit. The proof uses JUMPS14's fixed-mark theorem for the inserted mark and induction of finite sums, allocating half of each epsilon to the head and the tail. This directly addresses finite-atomic compensation before infinite-activity Levy integration, without assuming continuity across zero or atomlessness of the negative Levy measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps15_original_finite_negative_mark_Taylor_upperlim
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    let R : ℝ → ℝ → ℝ := fun a z =>
      w (a + z) - w a -
        (if -1 < z then z * deriv w a else 0)
    ∀ S : Finset ℝ, (∀ z ∈ S, z < 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        S.sum (fun z => R (u n) z) ≤ S.sum (fun z => R y z) + ε := by sorry
