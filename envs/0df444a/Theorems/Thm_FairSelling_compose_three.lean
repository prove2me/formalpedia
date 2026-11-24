-- Prove2me | Theorems.Thm_FairSelling_compose_three
-- name    : FairSelling.compose_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:12.343957+00:00
-- url     : https://prove2.me/theorems/bbe6759f-917d-4d8e-868f-edab3d460f2a
-- title:
--   Fair Selling: compose three
-- statement:
--   **Composition lemma.** Suppose agent `a` receives a bundle `Ka` (goods handed in full,
--   valued via `v̄`) plus force-sale money `ma` (backed by the proceeds of a disjoint sold set
--   `Sa`), worth at least `3/4 · MMS_a`.  Let `R` be the remaining goods.  If a valid two-agent
--   outcome on the *restricted* instance over `R` gives its two parts at least `3/4 · MMS_b` and
--   `3/4 · MMS_c` (measured with the restricted valuations), then there is a valid three-agent
--   outcome giving every agent at least `3/4` of its maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L94-L204
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L94-L204

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.compose_three (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (Ka Sa : Finset G) (ma : ℝ)
    (hKSa : Disjoint Ka Sa) (hma0 : 0 ≤ ma) (hmaS : ma ≤ ∑ g ∈ Sa, p g)
    (haU : (3/4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p Ka + ma)
    (o2 : Outcome G 2)
    (ho2 : o2.Valid (restrictVal (Finset.univ \ (Ka ∪ Sa)) p))
    (hb : (3/4 : ℝ) * MMS 3 (v b) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v b)) o2 0)
    (hc : (3/4 : ℝ) * MMS 3 (v c) p ≤
      util (restrictVal (Finset.univ \ (Ka ∪ Sa)) (v c)) o2 1) :
    ∃ o : Outcome G 3, o.Valid p ∧ ∀ i, (3/4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
