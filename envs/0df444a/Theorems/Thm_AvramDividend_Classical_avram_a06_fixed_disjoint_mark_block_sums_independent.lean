-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_disjoint_mark_block_sums_independent
-- name    : AvramDividend.Classical.avram_a06_fixed_disjoint_mark_block_sums_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:36:14.113166+00:00
-- url     : https://prove2.me/theorems/e5df9e82-2d21-46b8-9393-ffe76c52a4bc
-- title:
--   Sums on disjoint deterministic intervals of an independent mark stream remain independent
-- statement:
--   For arbitrary independent measurable real marks and any deterministic ordered finite grid of natural-number cut points, the sums of marks over successive disjoint half-open index intervals are mutually independent. No identical-distribution assumption is needed. This is the deterministic conditional-on-count-vector ingredient of the A06 random-block characteristic-factorisation child 23364f73, and can be proved by restricting the independent mark family to disjoint index sets (Proved 666d880d) and applying measurable finite sums.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_disjoint_mark_block_sums_independent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (m : Fin (n + 1) → ℕ) (hm : Monotone m)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, Measurable (Y k)) (hIndep : iIndepFun Y P) :
    iIndepFun (fun (i : Fin n) ω =>
      ∑ k ∈ Finset.Ico (m i.castSucc) (m i.succ), Y k ω) P := by sorry
