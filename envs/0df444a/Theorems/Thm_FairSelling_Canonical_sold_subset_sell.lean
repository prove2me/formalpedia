-- Prove2me | Theorems.Thm_FairSelling_Canonical_sold_subset_sell
-- name    : FairSelling.Canonical.sold_subset_sell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:34:15.750321+00:00
-- url     : https://prove2.me/theorems/6434913c-26f9-4e32-a37e-ef6d35a1a6dc
-- title:
--   Canonical: sold subset sell
-- statement:
--   The Canonical construction uses the sold subset sell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L227-L231
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L227-L231

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

theorem FairSelling.Canonical.sold_subset_sell (C : Canonical w p μ t k R D) (J : Finset (Fin k)) :
    C.sold J ⊆ C.sell := by sorry
