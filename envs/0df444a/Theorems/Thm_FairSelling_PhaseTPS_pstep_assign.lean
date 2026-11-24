-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pstep_assign
-- name    : FairSelling.PhaseTPS.pstep_assign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:00:44.695371+00:00
-- url     : https://prove2.me/theorems/0a5f5f63-1eb9-4883-a608-4fd8f9f7996a
-- title:
--   Phase TPS: pstep assign
-- statement:
--   **Handing a package to an agent.**  If `k` already holds a bundle, its old package is
--   released first: its goods return to the pool, the goods of `own k` are un-sold, and its money
--   goes back to the bank.  All the bookkeeping of the invariant is discharged here.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseStep.lean#L105-L518
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseStep.lean#L105-L518

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhase
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.pstep_assign (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) {k : Fin n}
    {S S₀own S₀ext : Finset G}
    (hSpool : S ⊆ s.pool) (hOpool : S₀own ⊆ s.pool) (hEpool : S₀ext ⊆ s.pool)
    (hSO : Disjoint S S₀own) (hSE : Disjoint S S₀ext) (hOE : Disjoint S₀own S₀ext)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hfin : q + r ≤ s.bank + (s.cash k + s.resv k - ∑ g ∈ s.own k, p g)
              + (∑ g ∈ S₀own, p g) + ∑ g ∈ S₀ext, p g)
    (hself : ∑ g ∈ S₀own, p g ≤ q + r)
    (hpure : (∀ g ∈ S₀ext, PureGood v p (insert k s.served) g) ∨
      (S = ∅ ∧ S₀own = ∅ ∧ r = 0 ∧ ∃ g0, S₀ext = {g0} ∧ q ≤ p g0))
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k → (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : ∀ j, j ∉ insert k s.served →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀own, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j)
    (hkpure : ∀ g ∈ s.ext k, PureGood v p s.served g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
