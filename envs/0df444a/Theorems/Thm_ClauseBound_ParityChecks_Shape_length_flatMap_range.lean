-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_length_flatMap_range
-- name    : ClauseBound.ParityChecks.Shape.length_flatMap_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:36.250925+00:00
-- url     : https://prove2.me/theorems/a5d32597-008e-47d9-a9fd-f4abcac439a6
-- title:
--   Shape: length flat Map range
-- statement:
--   The same for the whole list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L136-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L136-L142

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.length_flatMap_range {γ : Type} (f : ℕ → List γ) (j : ℕ) :
    ((List.range j).flatMap f).length = ∑ j' ∈ range j, (f j').length := by sorry
