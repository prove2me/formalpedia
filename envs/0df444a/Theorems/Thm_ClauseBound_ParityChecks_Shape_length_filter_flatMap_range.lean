-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_length_filter_flatMap_range
-- name    : ClauseBound.ParityChecks.Shape.length_filter_flatMap_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:28.631826+00:00
-- url     : https://prove2.me/theorems/33604b5a-c1f4-45ca-9249-63c9443b9c32
-- title:
--   Shape: length filter flat Map range
-- statement:
--   The members with a property of a list that is put together from pieces number 0, …, j − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L127-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L127-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.length_filter_flatMap_range {γ : Type} (f : ℕ → List γ) (P : γ → Bool) (j : ℕ) :
    (((List.range j).flatMap f).filter P).length = ∑ j' ∈ range j, ((f j').filter P).length := by sorry
