-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_length_filter_eq_card
-- name    : ClauseBound.ParityChecks.Shape.length_filter_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:00.790983+00:00
-- url     : https://prove2.me/theorems/5a7139af-8629-48b4-a9f0-39ddbdb12b41
-- title:
--   Shape: length filter eq card
-- statement:
--   The clauses with a property, counted by their numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L111-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L111-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.length_filter_eq_card (ψ : Fml) (P : List (ℕ × Bool) → Bool) :
    (ψ.filter P).length = #{x ∈ range ψ.length | P (ψ.getD x []) = true} := by sorry
