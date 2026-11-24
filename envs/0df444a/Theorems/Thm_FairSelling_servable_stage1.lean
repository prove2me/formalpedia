-- Prove2me | Theorems.Thm_FairSelling_servable_stage1
-- name    : FairSelling.servable_stage1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:13.379154+00:00
-- url     : https://prove2.me/theorems/8fc4c1b9-dff6-4028-a147-187ef2da49c8
-- title:
--   Fair Selling: servable stage1
-- statement:
--   **The first stage of the preliminary phase.**  While some available good is priced above the
--   threshold of some active agent, sell it and pay its threshold to the active agent of lowest
--   maximin share (which, having the lowest threshold, is also happy with that good's price).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L137-L166
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L137-L166

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

theorem FairSelling.servable_stage1 (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      Losses v p T R D → Servable v p (thr v p) T R D := by sorry
