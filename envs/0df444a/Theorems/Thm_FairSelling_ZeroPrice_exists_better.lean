-- Prove2me | Theorems.Thm_FairSelling_ZeroPrice_exists_better
-- name    : FairSelling.ZeroPrice.exists_better
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:55:45.534589+00:00
-- url     : https://prove2.me/theorems/5606b103-e060-403f-9978-94dddf68cd3c
-- title:
--   Zero Price: exists better
-- statement:
--   **The improvement step.**  From a legitimate state in which some agent is unserved one can
--   build a legitimate state that serves one more agent, or serves the same agents with a strictly
--   larger total value.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L260-L385
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxZero.lean#L260-L385

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxZero
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ZeroPrice
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.ZeroPrice.exists_better (v : Fin n → G → ℝ) (p : G → ℝ) (hp0 : ∀ g, p g = 0)
    (hv : ∀ i g, 0 ≤ v i g) (hn : 0 < n) (s : St G n) (hs : GoodSt v p s)
    (hT : s.1 ≠ Finset.univ) :
    ∃ s' : St G n, GoodSt v p s' ∧
      (s.1.card < s'.1.card ∨
        (s'.1.card = s.1.card ∧ ∑ i, bval (v i) (s.2 i) < ∑ i, bval (v i) (s'.2 i))) := by sorry
