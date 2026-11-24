-- Prove2me | Theorems.Thm_FairSelling_outcome_of_assignment
-- name    : FairSelling.outcome_of_assignment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:06:30.126085+00:00
-- url     : https://prove2.me/theorems/bbe9b1f7-f112-48c2-852a-06dc09c58832
-- title:
--   Fair Selling: outcome of assignment
-- statement:
--   **Allocating three bundles of a canonical partition to the three agents.**  If each agent `i`
--   accepts the bundle `ka i` assigned to it, and the assignment is a bijection, the resulting
--   allocation (executing the proposed sale) is a valid `3/4`-MMS outcome.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L276-L309
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean#L276-L309

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
omit [Fintype G]

theorem FairSelling.outcome_of_assignment (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    {w : G → ℝ} {τ : ℝ} {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ}
    {lo : Fin 3} (hcan : IsCanonical w p τ kept sold money lo)
    (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (kx ky kz : Fin 3) (hkxy : kx ≠ ky) (hkxz : kx ≠ kz) (hkyz : ky ≠ kz)
    (hx : (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p (kept kx) + money kx)
    (hy : (3 / 4 : ℝ) * MMS 3 (v y) p ≤ vbarSum (v y) p (kept ky) + money ky)
    (hz : (3 / 4 : ℝ) * MMS 3 (v z) p ≤ vbarSum (v z) p (kept kz) + money kz) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by sorry
