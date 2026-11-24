-- Prove2me | Theorems.Thm_FairSelling_servable_stage2
-- name    : FairSelling.servable_stage2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:29.84499+00:00
-- url     : https://prove2.me/theorems/bb198500-2f30-4a77-9c4b-c72c3d1e946c
-- title:
--   Fair Selling: servable stage2
-- statement:
--   **The second stage of the preliminary phase.**  While some active agent values an available
--   good above its threshold, hand the good over to that agent.  When no such good is left, and given
--   that the first stage is over, no available good is worth as much as the threshold to an active
--   agent, so the invariant of the main loop holds.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L97-L132
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L97-L132

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.servable_stage2 (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      Losses v p T R D → (∀ a ∈ T, ∀ e ∈ R, p e < thr v p a) →
      Servable v p (thr v p) T R D := by sorry
