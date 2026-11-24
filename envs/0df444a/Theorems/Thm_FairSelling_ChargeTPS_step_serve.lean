-- Prove2me | Theorems.Thm_FairSelling_ChargeTPS_step_serve
-- name    : FairSelling.ChargeTPS.step_serve
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:58:23.423633+00:00
-- url     : https://prove2.me/theorems/b18c2efb-aade-4f2f-b83e-8191e4384fec
-- title:
--   Charge TPS: step serve
-- statement:
--   **Handing a package to an unserved agent.**  All the hypotheses are the invariants that the
--   new package has to satisfy on its own; everything else is bookkeeping.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L85-L252
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxServe.lean#L85-L252

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage

theorem FairSelling.ChargeTPS.step_serve (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    {s : CStage G n} (hs : s.Good v p eps)
    {k : Fin n} (hk : k ∉ s.served)
    {S S₀ : Finset G} (hSpool : S ⊆ s.pool) (hS₀pool : S₀ ⊆ s.pool) (hSS₀ : Disjoint S S₀)
    {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hbank : 0 ≤ s.bank + (∑ g ∈ S₀, p g) - q - r)
    (hclaim : GeneralTPS.thr v p k ≤ vbarSum (v k) p S + q)
    (hkeep : ∀ g ∈ S, p g ≤ v k g)
    (hsafenew : ∀ j, j ≠ k →
      (vbarSum (v j) p S + q ≤ s.req v p eps j) ∨
      (q = 0 ∧ ∀ g ∈ S, vbarSum (v j) p (S \ {g}) + p g ≤ s.req v p eps j))
    (hcostnew : ∀ j, j ∉ s.served → j ≠ k →
      truncBundle (v j) p (TPS n (v j) p) S + q + r
        + ∑ g ∈ S₀, saleLoss (v j) p (TPS n (v j) p) g ≤ 2 * GeneralTPS.thr v p j) :
    ∃ s' : CStage G n, s'.Good v p eps ∧ s.served.card < s'.served.card := by sorry
