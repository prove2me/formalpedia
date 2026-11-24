-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_pmoney_step
-- name    : FairSelling.PhaseTPS.pmoney_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:00:41.644051+00:00
-- url     : https://prove2.me/theorems/4f9cfa42-04a1-4825-b848-b4689090805b
-- title:
--   Phase TPS: pmoney step
-- statement:
--   **The moving-knife step of Algorithm 6** — the two large-good loops.
--
--   A set `F` of *pure* pool goods is sold, and the claimant receives the least slice `Qc(∅)` of the
--   proceeds that makes somebody claim it, the rest staying in the bank, available to the other
--   agents.  This is the manuscript's moving knife, and it is the reason the loss to the agents that
--   are *not* served by the step is limited: selling a pure good costs nobody anything, and the
--   slice that is handed out is at most the threshold of every unserved agent.
--
--   The step is stated for an arbitrary set `F` of pure goods, and in particular covers
--
--   * `F = ∅` — the slice is paid for out of the free proceeds already in the bank, with nothing
--     sold at all;
--   * `F` a single good — the manuscript's price loop for a good whose price already dominates the
--     truncated contribution of every unserved agent (`plarge_pure_step` below).
--
--   Several agents may be served, one after another, out of the proceeds of a single sold good: this
--   is the *sharing* that the large-good loops allow, and it is harmless here because every bundle
--   handed out is a slice of the proceeds of a set of goods that cost their sellers nothing.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L106-L146
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhaseImp.lean#L106-L146

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.PhaseTPS.pmoney_step (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) (k0 : Fin n)
    {F : Finset G} (hFpool : F ⊆ s.pool)
    (hFpure : ∀ g ∈ F, PureGood v p s.served g)
    (hafford : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.bank + ∑ g ∈ F, p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by sorry
