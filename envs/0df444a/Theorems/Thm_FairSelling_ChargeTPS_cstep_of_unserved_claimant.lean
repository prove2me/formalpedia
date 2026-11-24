-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_cstep_of_unserved_claimant
-- name    : FairSelling.ChargeTPS.cstep_of_unserved_claimant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:51.403799+00:00
-- url     : https://prove2.me/theorems/53c88d00-6342-43b8-bbbe-1924e16d96cc
-- title:
--   Charge TPS: cstep of unserved claimant
-- statement:
--   **The bag-filling case of the improvement step.**  If the minimal admissible package built out
--   of the pool is claimed by an agent that is not yet served, then handing it over serves one more
--   agent.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L242-L278
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxStep.lean#L242-L278

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)

theorem FairSelling.ChargeTPS.cstep_of_unserved_claimant (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : CStage G n} (hs : s.Good v p eps) {k0 : Fin n}
    {S S₀ : Finset G} (hUP : S ∪ S₀ ⊆ s.pool) (hdisj : Disjoint S S₀)
    (hadm : CfgTPS.Adm v p (s.req v p eps) k0 s.bank S S₀)
    (hmin : ∀ T T₀ : Finset G, T ∪ T₀ ⊆ s.pool → Disjoint T T₀ →
      CfgTPS.Adm v p (s.req v p eps) k0 s.bank T T₀ →
      (S ∪ S₀).card * (s.pool.card + 1) + S₀.card
        ≤ (T ∪ T₀).card * (s.pool.card + 1) + T₀.card)
    {k : Fin n} (hk : k ∉ s.served)
    (hclaim : s.req v p eps k ≤ vbarSum (v k) p S + CfgTPS.Qc v p (s.req v p eps) k0 S) :
    ∃ s' : CStage G n, s'.Good v p eps ∧ s.served.card < s'.served.card := by sorry
