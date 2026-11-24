-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsExampleFour_no_better_than_one_over_n
-- name    : FairSelling.EqualProceedsExampleFour.no_better_than_one_over_n
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:33:31.486098+00:00
-- url     : https://prove2.me/theorems/5ee29b78-5b9a-46aa-bbc3-94b35b7a65be
-- title:
--   Equal Proceeds Example Four: no better than one over n
-- statement:
--   **Example 4**: for every `ε > 0` there is an instance (all prices `1`, agent `1` valuing
--   every good at `1/L` and the others at `L`, for a large `L`) in which every valid equal-proceeds
--   outcome leaves some agent below `(1/n + ε)` times her equal-proceeds maximin share.  Hence no
--   approximation better than `1/n` of the equal-proceeds MMS can be guaranteed.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L308-L398
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L308-L398

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)

theorem FairSelling.EqualProceedsExampleFour.no_better_than_one_over_n (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ o : Outcome (Fin (N + 2)) (N + 2),
      o.Valid (price N) → o.EqualProceeds (price N) →
      ∃ i, util (val N L i) o i
            < (1 / ((N : ℝ) + 2) + ε) * MMSEP (N + 2) (val N L i) (price N) := by sorry
