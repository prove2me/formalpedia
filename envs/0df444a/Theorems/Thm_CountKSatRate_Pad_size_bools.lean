-- Prove2me | Theorems.Thm_CountKSatRate_Pad_size_bools
-- name    : CountKSatRate.Pad.size_bools
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:45.374929+00:00
-- url     : https://prove2.me/theorems/7584200b-f78d-4d8c-b2ee-8b4b24ccb137
-- title:
--   Pad: size bools
-- statement:
--   The size of a bit string.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L43-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L43-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_bools
import Theorems.Thm_PaddedDescent_size_bools
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}

theorem CountKSatRate.Pad.size_bools (x : List Bool) : size x = 2 * x.length + 1 := by sorry
