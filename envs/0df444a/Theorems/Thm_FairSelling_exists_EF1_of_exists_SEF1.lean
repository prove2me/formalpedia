-- Prove2me | Theorems.Thm_FairSelling_exists_EF1_of_exists_SEF1
-- name    : FairSelling.exists_EF1_of_exists_SEF1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:15:53.4658+00:00
-- url     : https://prove2.me/theorems/512408d9-08b3-40d3-b05e-4378b6353d50
-- title:
--   Fair Selling: exists EF1 of exists SEF1
-- statement:
--   **Lemma 10, direction `SEF1 ⟹ EF1`.**
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L191-L197
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L191-L197

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_EF1_of_exists_SEF1
    (hSEF1 : ∀ w : Fin n → G → ℝ, (∀ i g, 0 ≤ w i g) →
      ∃ o : Outcome G n, o.Full (fun _ => 0) ∅ ∧ SEF1 w (fun _ => 0) o)
    (v : Fin n → G → ℝ) (hv : ∀ i g, 0 ≤ v i g) :
    ∃ A : Fin n → Finset G, IsPartitionOf A Finset.univ ∧ EF1alloc v A := by sorry
