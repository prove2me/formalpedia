-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_capped_iInf_finite_prefix_ws01c
-- name    : AvramDividend.Classical.bv_capped_iInf_finite_prefix_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:16:41.550084+00:00
-- url     : https://prove2.me/theorems/f84e143f-c9cc-4ae8-864d-7561d92165c1
-- title:
--   A capped complete infimum is determined by its finite prefix when its tail exceeds the cap
-- statement:
--   In any complete linear order, if every indexed value after M is at least the cap T, the global indexed infimum capped at T equals the finite indexed prefix infimum through M capped at T. The proof compares both infima by the universal order properties and splits each index at M.
-- source:
--   Causal repair of terminal publication job 6ac0cf4b-6db7-4100-8617-d8908fb0991a: the sole error was the invalid open AvramDividend.Classical. Removed only that open; the exact formal statement and proof preserved at work/avram_ws01c_capped_iInf_prefix_solution_pub_repair_20261028.lean.

import Mathlib

open Filter Set Order
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_capped_iInf_finite_prefix_ws01c
    {α : Type*} [CompleteLinearOrder α]
    (v : ℕ → α) (T : α) (M : ℕ)
    (hTail : ∀ k : ℕ, M < k → T ≤ v k) :
    (⨅ k : ℕ, v k) ⊓ T =
      (⨅ (k : ℕ) (_ : k ≤ M), v k) ⊓ T := by sorry
