-- Prove2me | Theorems.Thm_FairSelling_compose_three_cash
-- name    : FairSelling.compose_three_cash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:15.986257+00:00
-- url     : https://prove2.me/theorems/11ed3773-4442-4112-a585-a0db3a430d7f
-- title:
--   Fair Selling: compose three cash
-- statement:
--   The Fair Selling construction uses the compose three cash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L161-L180
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L161-L180

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.compose_three_cash (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hcash0 : 0 ≤ cash)
    (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome (Option G) 2)
    (ho2 : o2.Valid (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash))
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      util (cashVal (Finset.univ \ (Ka ∪ Sa)) (v d)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
