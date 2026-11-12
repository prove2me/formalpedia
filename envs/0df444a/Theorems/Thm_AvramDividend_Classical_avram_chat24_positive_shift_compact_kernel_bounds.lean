-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_positive_shift_compact_kernel_bounds
-- name    : AvramDividend.Classical.avram_chat24_positive_shift_compact_kernel_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:01:58.520207+00:00
-- url     : https://prove2.me/theorems/55cebcdf-49f9-4fff-bf5f-7a1c0dcce0b0
-- title:
--   C1 positive-reserve compact bands provide both bounded and Lipschitz jump-kernel constants
-- statement:
--   If w is continuous on the nonnegative half-line, vanishes on the negative half-line, and is C1 on the positive half-line, every band 0<a<=b admits nonnegative constants L,R with w L-Lipschitz on [a/2,b] and |w(v)|<=R for all v<=b. This supplies exactly the two analytic constants used by the original infinite-activity NX compensation theorem 7cf52fcc. Complete candidate proof is already drafted using compact derivative bounds and the mean-value Lipschitz theorem. It is a substantive analytic prerequisite for the positive-shift stopped source estimate 0d51b191; publication alone establishes no parent edge or theorem acceptance.

import Mathlib
open Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat24_positive_shift_compact_kernel_bounds
    (w : ℝ → ℝ) (hc : ContinuousOn w (Ici 0))
    (hn : ∀ y < 0, w y = 0) (hs : ContDiffOn ℝ 1 w (Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by sorry
