-- Prove2me | Theorems.Thm_FairSelling_exit_count
-- name    : FairSelling.exit_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:13:23.315816+00:00
-- url     : https://prove2.me/theorems/646db113-4685-4047-a10b-4652acc7d8ae
-- title:
--   Fair Selling: exit count
-- statement:
--   **The counting at the end of the descent.**  When every surviving bundle carries at most one
--   witness good and at most one large available good, and at most one bundle carries both, the large
--   available goods are at most `|J| − |Q| + 1` in number.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L122-L191
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L122-L191

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
import Definitions.Def_RequestProject_TwoThirdsDescent
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
omit [Fintype G]

theorem FairSelling.exit_count (bg : ι → Finset G) (hbdisj : ∀ j j', j ≠ j' → Disjoint (bg j) (bg j'))
    (bidx : κ → ι) {J : Finset ι} {Q : Finset κ} {Lset : Finset G}
    (hQJ : ∀ b ∈ Q, bidx b ∈ J)
    (hLJ : ∀ g ∈ Lset, ∃ j ∈ J, g ∈ bg j)
    (h1 : ∀ j ∈ J, (Q.filter (fun b => bidx b = j)).card ≤ 1)
    (h2 : ∀ j ∈ J, (Lset.filter (fun g => g ∈ bg j)).card ≤ 1)
    (h3 : (J.filter (fun j => (Q.filter (fun b => bidx b = j)).Nonempty ∧
        (Lset.filter (fun g => g ∈ bg j)).Nonempty)).card ≤ 1) :
    Lset.card + Q.card ≤ J.card + 1 := by sorry
