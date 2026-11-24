-- Prove2me | Theorems.Thm_FairSelling_losses_extend
-- name    : FairSelling.losses_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:05.47959+00:00
-- url     : https://prove2.me/theorems/4db60798-5582-4a7d-936e-0874c4cfc003
-- title:
--   Fair Selling: losses extend
-- statement:
--   Extending the accounting by a single event.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L268-L286
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L268-L286

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

theorem FairSelling.losses_extend (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D) {a : Fin n} (ha : a ∈ T)
    (E F : Finset G) (c : ℝ) (hE : E ⊆ R) (hF : F ⊆ R) (hEF : Disjoint E F) (hc : 0 ≤ c)
    (htype : ∀ i ∈ T.erase a, ∀ Ei : EquiMMS (v i) p (MMS n (v i) p) n,
      LossOK (v i) p Ei.sell (MMS n (v i) p) (thr v p i) E F c) :
    Losses v p (T.erase a) (R \ (E ∪ F)) (D + (∑ g ∈ F, p g) - c) := by sorry
