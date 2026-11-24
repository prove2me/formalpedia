-- Prove2me | Theorems.Thm_FairSelling_MMS2_cash_of_one_good_loss
-- name    : FairSelling.MMS2_cash_of_one_good_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:09:56.440906+00:00
-- url     : https://prove2.me/theorems/d57188cd-55dc-4b4b-9542-adfff3be5a51
-- title:
--   Fair Selling: MMS2 cash of one good loss
-- statement:
--   **A single good, and some money, taken out of the pool.**  Suppose one good `e` is removed
--   (sold or handed to somebody else), the cash `c` is banked, and the money `m ≤ p e` that has been
--   paid out is at most `3/4 · MMS`, the banked cash covering the rest of the price of `e`
--   (`p e ≤ c + m`).  Then the agent can still split the remaining goods and the banked cash into two
--   bundles worth `3/4 · MMS` each.
--
--   This covers both stages of the preliminary phase: stage 1 with `m = 3/4 · MMSⱼ` and
--   `c = p e - m`, and stage 2 with `m = p e` and `c = 0`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L45-L155
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/PreliminaryPhase.lean#L45-L155

import Mathlib
import Definitions.Def_RequestProject_LemmaFourResidual
import Definitions.Def_RequestProject_PreliminaryPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.MMS2_cash_of_one_good_loss (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (e : G) (c m : ℝ) (hc : 0 ≤ c) (hm0 : 0 ≤ m)
    (hmτ : m ≤ (3 / 4 : ℝ) * MMS 3 w p) (hme : m ≤ p e) (hcm : p e ≤ c + m) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ {e}) w)
      (cashPrice (Finset.univ \ {e}) p c) := by sorry
