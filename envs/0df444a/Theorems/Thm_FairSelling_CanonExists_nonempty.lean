-- Prove2me | Theorems.Thm_FairSelling_CanonExists_nonempty
-- name    : FairSelling.CanonExists.nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:30.057264+00:00
-- url     : https://prove2.me/theorems/29535726-c4d1-49b6-94bf-d698bfacb307
-- title:
--   Canon Exists: nonempty
-- statement:
--   With a `NeZero` instance at hand, `CanonExists` is the existence of a canonical partition.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L36-L38
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L36-L38

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

theorem FairSelling.CanonExists.nonempty {w p : G → ℝ} {μ t : ℝ} {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ}
    (h : CanonExists w p μ t k R D) : Nonempty (Canonical w p μ t k R D) := by sorry
