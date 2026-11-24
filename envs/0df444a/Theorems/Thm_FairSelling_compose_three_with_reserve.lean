-- Prove2me | Theorems.Thm_FairSelling_compose_three_with_reserve
-- name    : FairSelling.compose_three_with_reserve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:04.035413+00:00
-- url     : https://prove2.me/theorems/a5fb8d38-ba3b-4d2b-90fe-9f78465dda91
-- title:
--   Fair Selling: compose three with reserve
-- statement:
--   The Fair Selling construction uses the compose three with reserve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L99-L155
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L99-L155

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.compose_three_with_reserve (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome G 2)
    (ho2sold : ∀ i, Disjoint o2.sold (o2.kept i))
    (ho2disj : ∀ i j, i ≠ j → Disjoint (o2.kept i) (o2.kept j))
    (ho2money : ∀ i, 0 ≤ o2.money i)
    (ho2budget : ∑ i, o2.money i ≤
      ∑ g ∈ o2.sold, restrictVal (Finset.univ \ (Ka ∪ Sa)) p g + cash)
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v d)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
