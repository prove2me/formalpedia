-- Prove2me | Theorems.Thm_CountKSatRate_Pad_len_padded
-- name    : CountKSatRate.Pad.len_padded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:00.64308+00:00
-- url     : https://prove2.me/theorems/814ba66e-cfa8-4d55-aedc-9fd66a265bbe
-- title:
--   Pad: len padded
-- statement:
--   The word of (x, pad of length 2^k) has 3|x| + 4·2^k + 6 symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L91-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L91-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}

theorem CountKSatRate.Pad.len_padded (x : List Bool) (k : ℕ) : len (x, pad k) = 3 * x.length + 4 * 2 ^ k + 6 := by sorry
