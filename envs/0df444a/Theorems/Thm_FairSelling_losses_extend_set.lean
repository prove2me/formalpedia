-- Prove2me | Theorems.Thm_FairSelling_losses_extend_set
-- name    : FairSelling.losses_extend_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:45:53.96594+00:00
-- url     : https://prove2.me/theorems/08836876-b6e5-4c0a-a36a-27d50c167367
-- title:
--   Fair Selling: losses extend set
-- statement:
--   **Extending the accounting by one round.**  The agents of `Kset` are served: agent `b` gets
--   the goods `Ea b` and `ca b` units of money, and the goods `Fa b` are sold in the process.  If
--   every still-active agent sees each of these events as a loss of one of the four types, the new
--   state is accounted for.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L170-L265
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L170-L265

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.losses_extend_set (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D) {Kset : Finset (Fin n)} (hKT : Kset ⊆ T)
    (Ea Fa : Fin n → Finset G) (ca : Fin n → ℝ)
    (hEsub : ∀ b ∈ Kset, Ea b ⊆ R) (hFsub : ∀ b ∈ Kset, Fa b ⊆ R)
    (hEF : ∀ b ∈ Kset, Disjoint (Ea b) (Fa b))
    (hpair : ∀ b ∈ Kset, ∀ b' ∈ Kset, b ≠ b' → Disjoint (Ea b ∪ Fa b) (Ea b' ∪ Fa b'))
    (hc0 : ∀ b ∈ Kset, 0 ≤ ca b)
    (htype : ∀ i ∈ T \ Kset, ∀ Ei : EquiMMS (v i) p (MMS n (v i) p) n, ∀ b ∈ Kset,
      LossOK (v i) p Ei.sell (MMS n (v i) p) (thr v p i) (Ea b) (Fa b) (ca b)) :
    Losses v p (T \ Kset) (R \ Kset.biUnion (fun b => Ea b ∪ Fa b))
      (D + (∑ b ∈ Kset, ∑ g ∈ Fa b, p g) - ∑ b ∈ Kset, ca b) := by sorry
