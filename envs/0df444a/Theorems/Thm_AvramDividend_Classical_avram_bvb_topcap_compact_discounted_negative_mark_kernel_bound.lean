-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_compact_discounted_negative_mark_kernel_bound
-- name    : AvramDividend.Classical.avram_bvb_topcap_compact_discounted_negative_mark_kernel_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:06:51.232195+00:00
-- url     : https://prove2.me/theorems/1770123f-713e-4d5d-9030-e46df2a2c1c1
-- title:
--   Uniform discounted negative-mark value loss on every compact nonnegative reserve band
-- statement:
--   For any continuous nonnegative-reserve reward vanishing at negative reserve, discount q nonnegative, finite reserve upper bound B, the discounted negative-mark value increment is uniformly absolutely bounded for every t>=0 and every negative mark, including b=0. Needed to dominate original topcap physical and compensator negative-mark kernels.
-- source:
--   Derived from proved compact value bound 007afc48 and elementary nonnegative discount factor. No finite dividend cap and no process substitution. Target marked original jump count majorant child 553da8cc.

import Mathlib
open Set MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_bvb_topcap_compact_discounted_negative_mark_kernel_bound
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (t b z : ℝ), 0 ≤ t → 0 ≤ b → b ≤ B → z < 0 →
        |Real.exp (-(q * t)) * (w (b + z) - w b)| ≤ K := by sorry
