-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_foldr_min_eq_finite_iInf_ws01c
-- name    : AvramDividend.Classical.bv_foldr_min_eq_finite_iInf_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:16:37.779927+00:00
-- url     : https://prove2.me/theorems/2ce8bfa7-fbc8-4250-b464-0964b97febf1
-- title:
--   Finite-list binary minimum fold equals the indexed infimum with fallback
-- statement:
--   For a complete linear order, a fold taking the binary minimum of values at finitely many natural indices and a fallback H equals the indexed infimum restricted to those list indices, infimum H. The proof is a list induction respecting repeated indices; this is the bridge between executable finite grid observation folds and declarative indexed infima.
-- source:
--   Causal repair of terminal publication job 58644f06-30c8-4a46-9104-8fbd0118bbe6: the sole error was the invalid open AvramDividend.Classical. Removed only that open; the exact formal statement and proof preserved at work/avram_ws01c_foldr_min_iInf_solution_pub_repair_20261028.lean.

import Mathlib

open Set
open scoped ENNReal

theorem AvramDividend.Classical.bv_foldr_min_eq_finite_iInf_ws01c
    {α : Type*} [CompleteLinearOrder α]
    (v : ℕ → α) (L : List ℕ) (H : α) :
    L.foldr (fun k u => v k ⊓ u) H =
      (⨅ (j : ℕ) (_ : j ∈ L), v j) ⊓ H := by sorry
