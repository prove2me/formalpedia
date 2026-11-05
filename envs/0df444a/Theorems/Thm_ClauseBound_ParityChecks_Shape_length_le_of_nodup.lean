-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_length_le_of_nodup
-- name    : ClauseBound.ParityChecks.Shape.length_le_of_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:40.874541+00:00
-- url     : https://prove2.me/theorems/9f68b187-0442-406a-9699-06739d83fd90
-- title:
--   Shape: length le of nodup
-- statement:
--   A list without repetition of numbers below m has at most m members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L164-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L164-L166

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.length_le_of_nodup {L : List ℕ} (hL : L.Nodup) {m : ℕ} (hm : ∀ x ∈ L, x < m) : L.length ≤ m := by sorry
