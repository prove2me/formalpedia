-- Prove2me | Theorems.Thm_CountKSatRate_Pad_length_pad
-- name    : CountKSatRate.Pad.length_pad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:37:05.746467+00:00
-- url     : https://prove2.me/theorems/1c478b37-5bdc-476a-9502-6a4f5c07e1ab
-- title:
--   Pad: length pad
-- statement:
--   The length of the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L57-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L57-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_length_pad
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}

theorem CountKSatRate.Pad.length_pad (k : ℕ) : (pad k).length = 2 ^ k := by sorry
