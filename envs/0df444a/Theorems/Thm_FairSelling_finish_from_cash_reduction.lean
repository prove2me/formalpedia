-- Prove2me | Theorems.Thm_FairSelling_finish_from_cash_reduction
-- name    : FairSelling.finish_from_cash_reduction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:33:19.127089+00:00
-- url     : https://prove2.me/theorems/f479636e-a968-42f6-b2ce-03514a6b3c07
-- title:
--   Fair Selling: finish from cash reduction
-- statement:
--   The Fair Selling construction uses the finish from cash reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L186-L207
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgentCashComposition.lean#L186-L207

import Mathlib
import Definitions.Def_RequestProject_ThreeAgentCash
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.finish_from_cash_reduction (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (Ka Sa : Finset G) (ma cash : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hcash0 : 0 ≤ cash)
    (hbudget : ma + cash ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (hRb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v b))
        (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash))
    (hRd : (3/4 : ℝ) * MMS 3 (v d) p ≤
      MMS 2 (cashVal (Finset.univ \ (Ka ∪ Sa)) (v d))
        (cashPrice (Finset.univ \ (Ka ∪ Sa)) p cash)) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
