-- Prove2me | Theorems.Thm_FairSelling_finish_from_reduction
-- name    : FairSelling.finish_from_reduction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:36:41.567556+00:00
-- url     : https://prove2.me/theorems/85cc0a0f-1a13-40a7-b19f-8a4dbf782949
-- title:
--   Fair Selling: finish from reduction
-- statement:
--   Given the reduction data for a *specific* choice of the served agent `a` and the two other
--   agents `b, c`, finish the argument by running the two-agent algorithm on the restricted
--   instance and composing.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L209-L236
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L209-L236

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.finish_from_reduction (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Ka Sa : Finset G) (ma : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hmaS : ma ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (hRb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      MMS 2 (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b))
        (restrictVal (Finset.univ \ (Ka ∪ Sa)) p))
    (hRc : (3/4 : ℝ) * MMS 3 (v c) p ≤
      MMS 2 (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v c))
        (restrictVal (Finset.univ \ (Ka ∪ Sa)) p)) :
    ∃ o : Outcome G 3, o.Valid p ∧ ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
