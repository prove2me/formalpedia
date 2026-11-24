-- Prove2me | Theorems.Thm_FairSelling_Canonical_mem_sold
-- name    : FairSelling.Canonical.mem_sold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:51.086134+00:00
-- url     : https://prove2.me/theorems/e217c3a5-e8b9-4b63-b391-55d0a13757ff
-- title:
--   Canonical: mem sold
-- statement:
--   The Canonical construction uses the mem sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L222-L224
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L222-L224

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.Canonical
variable {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
omit [Fintype G]

theorem FairSelling.Canonical.mem_sold {C : Canonical w p μ t k R D} {J : Finset (Fin k)} {f : G} :
    f ∈ C.sold J ↔ ∃ j ∈ J, C.src j = some f := by sorry
