-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_nb_le
-- name    : CircuitLowerBound.Round.nb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:59:41.645752+00:00
-- url     : https://prove2.me/theorems/de04f9fe-9dbe-44e5-bd1f-25e9296d6a09
-- title:
--   Round: nb le
-- statement:
--   The number of a clause of the formula of the table of m, for variables of m bits, has at most 2m
--   bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L236-L242
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L236-L242

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

theorem CircuitLowerBound.Round.nb_le {m P : ℕ} (h : Fits (codeOf (nu m)) m P) : nb (codeOf (nu m)) m ≤ 2 * m := by sorry
