-- Prove2me | Theorems.Thm_FairSelling_cutgive
-- name    : FairSelling.cutgive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:10.856621+00:00
-- url     : https://prove2.me/theorems/2336e951-ff9f-4681-aaad-2cb8c47c60e5
-- title:
--   Fair Selling: cutgive
-- statement:
--   **Cut & Give** (the heart of the two-agent argument). If agent `0` (the *cutter*) has a
--   canonical MMS partition with a lower-priced split good than agent `1` (the *giver*), then there
--   is a valid outcome giving agent `0` at least `MMS0` and agent `1` at least `MMS1`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L246-L300
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L246-L300

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.cutgive (v : Fin 2 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (Ac : Fin 2 → Finset G) (sc : Finset G) (qc : Fin 2 → ℝ)
    (hc : Config (v 0) p (MMS 2 (v 0) p) Ac sc qc)
    (sg : Finset G) (hsg : sg.card ≤ 1)
    (hbound : 2 * MMS 2 (v 1) p ≤ vbarSum (v 1) p (Finset.univ \ sg) + ∑ g ∈ sg, p g)
    (hcut : ∑ g ∈ sc, p g ≤ ∑ g ∈ sg, p g) :
    ∃ o : Outcome G 2, o.Valid p ∧
      MMS 2 (v 0) p ≤ util (v 0) o 0 ∧ MMS 2 (v 1) p ≤ util (v 1) o 1 := by sorry
