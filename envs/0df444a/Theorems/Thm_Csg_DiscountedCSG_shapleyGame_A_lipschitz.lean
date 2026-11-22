-- Prove2me | Theorems.Thm_Csg_DiscountedCSG_shapleyGame_A_lipschitz
-- name    : Csg.DiscountedCSG.shapleyGame_A_lipschitz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:08:48.425389+00:00
-- url     : https://prove2.me/theorems/02522f5b-6c40-4a7e-9b8f-d8ef663ff7df
-- title:
--   Discounted CSG: shapley Game A lipschitz
-- statement:
--   The discounted stage game's payoff matrix moves by at most `l * ε` when the continuation moves
--       by at most `ε`, entrywise. The reward term does not depend on `v`, so it cancels out of the
--       difference exactly, leaving `l` times `expect_lipschitz`'s bound. The `l`-scaled counterpart of
--       `CsgMonotone.lean`'s `stageGame_A_lipschitz`, and the step that turns a `1`-Lipschitz
--       continuation dependence into a genuine contraction.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L119-L128
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/Discounted.lean#L119-L128

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

theorem Csg.DiscountedCSG.shapleyGame_A_lipschitz {s : S} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', |v s' - w s'| ≤ ε) (a1 : A1) (a2 : A2) :
    |(D.shapleyGame s v).A a1 a2 - (D.shapleyGame s w).A a1 a2| ≤ D.l * ε := by sorry
