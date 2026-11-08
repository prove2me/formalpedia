-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_monotone_finite_mark_sum_iSup
-- name    : AvramDividend.Classical.avram_redux20_monotone_finite_mark_sum_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:45:34.742539+00:00
-- url     : https://prove2.me/theorems/19c21901-5263-4dca-b6d0-247715bc9c49
-- title:
--   Monotone finite marked-sum approximations commute with countable supremum
-- statement:
--   For a finite set of actual marked-jump times and a pointwise increasing sequence of nonnegative extended-real mark losses, the supremum of finite total losses is the sum of the pointwise suprema. This is the finite-support limit interchange required when promoting countable simple-mark approximations to the original strict-cutoff marked jump integral.
-- source:
--   Finite induction. For the insert step, both monotone sequences have a directed common upper stage max i j, so ENNReal.iSup_add_iSup commutes their sum with the common-stage supremum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_monotone_finite_mark_sum_iSup
    {α : Type*} (S : Finset α) (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ a, Monotone (fun n : ℕ => f n a)) :
    (⨆ n : ℕ, ∑ a ∈ S, f n a) =
      ∑ a ∈ S, (⨆ n : ℕ, f n a) := by sorry
