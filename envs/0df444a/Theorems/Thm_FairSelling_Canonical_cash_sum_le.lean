-- Prove2me | Theorems.Thm_FairSelling_Canonical_cash_sum_le
-- name    : FairSelling.Canonical.cash_sum_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:34.660233+00:00
-- url     : https://prove2.me/theorems/94311169-2a44-45cc-b4c6-72decff16857
-- title:
--   Canonical: cash sum le
-- statement:
--   The money handed out with the parts of `J` does not exceed the bank plus the proceeds of the
--   goods sold to fund them.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L240-L276
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L240-L276

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

theorem FairSelling.Canonical.cash_sum_le (C : Canonical w p μ t k R D) (J : Finset (Fin k)) :
    ∑ j ∈ J, C.cash j ≤ D + ∑ g ∈ C.sold J, p g := by sorry
