-- Prove2me | Theorems.Thm_FairSelling_exists_threequarter_MMS_three
-- name    : FairSelling.exists_threequarter_MMS_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:07:27.072816+00:00
-- url     : https://prove2.me/theorems/b2378105-d5cd-434f-80be-d44e25812b8c
-- title:
--   Fair Selling: exists threequarter MMS three
-- statement:
--   **The manuscript's `n = 3` theorem.** Every optional-selling instance with three agents and
--   non-negative additive values and prices admits a valid outcome (a selling decision, an allocation
--   of the kept goods, and a distribution of the sale proceeds) giving every agent at least `3/4` of
--   its maximin share with selling.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentTheorem.lean#L31-L48
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentTheorem.lean#L31-L48

import Mathlib
import Definitions.Def_RequestProject_PreliminaryPhase
import Definitions.Def_RequestProject_ThreeAgentTheorem
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.exists_threequarter_MMS_three (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
