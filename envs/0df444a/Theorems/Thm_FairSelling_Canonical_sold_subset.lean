-- Prove2me | Theorems.Thm_FairSelling_Canonical_sold_subset
-- name    : FairSelling.Canonical.sold_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:29.323181+00:00
-- url     : https://prove2.me/theorems/c0b6ab9d-d8ff-470e-8033-f408718af8d2
-- title:
--   Canonical: sold subset
-- statement:
--   The Canonical construction uses the sold subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L234-L235
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L234-L235

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

theorem FairSelling.Canonical.sold_subset (C : Canonical w p μ t k R D) (J : Finset (Fin k)) : C.sold J ⊆ R := by sorry
