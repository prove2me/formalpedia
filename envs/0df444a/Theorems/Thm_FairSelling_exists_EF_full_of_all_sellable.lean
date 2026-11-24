-- Prove2me | Theorems.Thm_FairSelling_exists_EF_full_of_all_sellable
-- name    : FairSelling.exists_EF_full_of_all_sellable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:15:36.544092+00:00
-- url     : https://prove2.me/theorems/c3c053cd-e358-4961-be62-29fab6dc1ede
-- title:
--   Fair Selling: exists EF full of all sellable
-- statement:
--   The observation preceding Lemma 10: if all goods are sellable, selling everything and
--   splitting the proceeds equally is a full allocation which is `EF` (and, vacuously, `SEFX`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L87-L105
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaTen.lean#L87-L105

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_EF_full_of_all_sellable (v : Fin n → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (hn : 0 < n) :
    ∃ o : Outcome G n, o.Full p Finset.univ ∧ EF v p o ∧ SEFX v p o := by sorry
