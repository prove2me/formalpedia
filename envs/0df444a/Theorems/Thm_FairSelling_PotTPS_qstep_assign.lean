-- Prove2me | Theorems.Thm_FairSelling_PotTPS_qstep_assign
-- name    : FairSelling.PotTPS.qstep_assign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:10.672798+00:00
-- url     : https://prove2.me/theorems/2ad783e2-351b-4dbb-9d56-b7bbeb4be500
-- title:
--   Pot TPS: qstep assign
-- statement:
--   **Handing a package to an agent.**
--
--   If `k` already holds a bundle, its old package is released first (`Unshrink`): the goods it
--   keeps return to the pool, the goods of `own k` are un-sold, its money goes back to the bank, and
--   its slice — if it holds one — goes back into the pot of its good, the good itself being un-sold
--   if `k` was its last holder.  All the bookkeeping of the invariant is discharged here.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotStep.lean#L91-L698
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPotStep.lean#L91-L698

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPot
import Definitions.Def_RequestProject_TPSSefxPotStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
set_option maxHeartbeats 4000000

theorem FairSelling.PotTPS.qstep_assign (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) {k : Fin n}
    {S S₀ Src Snew : Finset G} {q r : ℝ}
    (hSpool : S ⊆ s.pool) (hS₀pool : S₀ ⊆ s.pool) (hSS₀ : Disjoint S S₀)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hSrcCard : Src.card ≤ 1)
    (hSrcNe : Src ≠ ∅ → S = ∅ ∧ S₀ = ∅ ∧ r = 0)
    (hSnew : Snew = ∅ ∨ (Snew = Src ∧ Src ⊆ s.pool))
    (hSrcOld : Snew = ∅ → Src ⊆ s.cutSet)
    (hpotSrc : ∀ g ∈ Src, q ≤ s.pot p g)
    (hslice : Src ≠ ∅ → ∀ j, j ∉ s.served → q ≤ GeneralTPS.thr v p j)
    (hfin : Src = ∅ → q + r ≤ s.freeBank p + ∑ g ∈ S₀, p g)
    (hself : ∑ g ∈ S₀, p g ≤ q + r)
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k → (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : Src = ∅ → ∀ j, j ∉ insert k s.served →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
