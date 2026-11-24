-- Prove2me | Theorems.Thm_FairSelling_canonExists_of_nonempty
-- name    : FairSelling.canonExists_of_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:57.11083+00:00
-- url     : https://prove2.me/theorems/f6c7c144-3d3e-4af1-8506-56ecc27d725f
-- title:
--   Fair Selling: canon Exists of nonempty
-- statement:
--   The Fair Selling construction uses the canon Exists of nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L41-L43
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L41-L43

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.canonExists_of_nonempty {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
    (h : Nonempty (Canonical w p μ t k R D)) : CanonExists w p μ t k R D := by sorry
