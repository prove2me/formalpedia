-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_shapley_lipschitz
-- name    : Csg.DiscountedCSG.shapley_lipschitz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:08:59.866109+00:00
-- url     : https://prove2.me/theorems/31dcdf79-1176-4aa2-8a8b-6869a7740bd6
-- title:
--   Discounted CSG: shapley lipschitz
-- statement:
--   The Shapley operator moves by at most `l * ε` at each state when the continuation moves by at
--       most `ε`: `MatrixGame.abs_value_sub_le` applied to `shapleyGame_A_lipschitz`. The `l`-scaled
--       counterpart of `CsgMonotone.lean`'s `stageValue_lipschitz`, and the per-state form of the
--       contraction below.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L134-L137
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L134-L137

import Definitions.Def_Csg_CsgMonotone
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Csg_Discounted
set_option autoImplicit true
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Csg.DiscountedCSG
variable (D : DiscountedCSG S A1 A2)

theorem Csg.DiscountedCSG.shapley_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) : |D.shapley v s - D.shapley w s| ≤ D.l * ε := by sorry
