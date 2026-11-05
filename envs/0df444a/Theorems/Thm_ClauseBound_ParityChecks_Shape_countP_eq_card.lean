-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_countP_eq_card
-- name    : ClauseBound.ParityChecks.Shape.countP_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:49:25.956941+00:00
-- url     : https://prove2.me/theorems/ca1b8cde-09d9-4c03-9a11-c668f2b1c256
-- title:
--   Shape: count P eq card
-- statement:
--   The members with a property of a list without repetition of numbers below m, counted as a set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L102-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L102-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.countP_eq_card {L : List ℕ} (hL : L.Nodup) {m : ℕ} (hm : ∀ x ∈ L, x < m) (P : ℕ → Bool) :
    L.countP P = #{x ∈ range m | x ∈ L ∧ P x = true} := by sorry
