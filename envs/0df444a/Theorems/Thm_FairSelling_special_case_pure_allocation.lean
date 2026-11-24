-- Prove2me | Theorems.Thm_FairSelling_special_case_pure_allocation
-- name    : FairSelling.special_case_pure_allocation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:17.554441+00:00
-- url     : https://prove2.me/theorems/4ca19d04-29b9-4a9f-a0fd-9acf7485aedc
-- title:
--   Fair Selling: special case pure allocation
-- statement:
--   **The special case with a pure bundle.**  Suppose the partitioning agent `a` proposed a
--   canonical partition, agent `b` accepts the pure non-leftovers bundle `kA`, and agent `d` rejects
--   all three bundles.  Then a complete `3/4`-MMS allocation exists: `b` takes the pure bundle, and
--   the remaining value is split between `a` and `d` — either `a` takes the two other bundles and `d`
--   everything else (which then contains the force-sold goods, worth a lot to `d`), or the sale
--   proceeds alone already satisfy `a`, and `d` takes everything except the pure bundle and the
--   force-sold goods.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L462-L583
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L462-L583

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.special_case_pure_allocation (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonical (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo)
    (hcard : sold.card ≤ 2)
    (kA kB : Fin 3) (hkA : kA ≠ lo) (hkB : kB ≠ lo) (hkAB : kA ≠ kB)
    (hpure : money kA = 0)
    (hbacc : (3 / 4 : ℝ) * MMS 3 (v b) p ≤ vbarSum (v b) p (kept kA) + money kA)
    (hdrej : ∀ k, vbarSum (v d) p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 (v d) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
