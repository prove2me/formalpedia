-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_replicate_inj
-- name    : CircuitLowerBound.Round.replicate_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:58:20.35018+00:00
-- url     : https://prove2.me/theorems/43bd2029-e296-4829-9070-d7f5f19ef2e2
-- title:
--   Round: replicate inj
-- statement:
--   The Round construction uses the replicate inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L147-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L147-L159

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round

theorem CircuitLowerBound.Round.replicate_inj {v v' : ℕ} {Y Y' : List Bool} (h : List.replicate v true ++ false :: Y = List.replicate v' true ++ false :: Y') : v = v' ∧ Y = Y' := by sorry
