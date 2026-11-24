-- Prove2me | Theorems.Thm_FairSelling_canonical_cons
-- name    : FairSelling.canonical_cons
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:13:16.522907+00:00
-- url     : https://prove2.me/theorems/d0d31cda-d450-4cb2-afc4-72af920cc8dd
-- title:
--   Fair Selling: canonical cons
-- statement:
--   **Adding one pure part.**  If a canonical `k`-partition of `(R', D)` exists and `new` is a set
--   of available goods, disjoint from `R'`, that is acceptable on its own, then a canonical
--   `(k+1)`-partition of `(R, D)` exists: the new part is added at the last index (or, when `k = 0`,
--   becomes the special part).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L67-L217
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsGlue.lean#L67-L217

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

theorem FairSelling.canonical_cons {w p : G → ℝ} {μ t : ℝ} {k : ℕ} {R R' new : Finset G} {D : ℝ}
    (hD : 0 ≤ D) (hR' : R' ⊆ R) (hnew : new ⊆ R) (hdisj : Disjoint new R')
    (hacc : t ≤ vbarSum w p new)
    (h : CanonExists w p μ t k R' D) :
    CanonExists w p μ t (k + 1) R D := by sorry
