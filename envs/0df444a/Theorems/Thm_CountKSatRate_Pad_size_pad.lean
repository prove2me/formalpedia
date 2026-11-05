-- Prove2me | Theorems.Thm_CountKSatRate_Pad_size_pad
-- name    : CountKSatRate.Pad.size_pad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:04.972217+00:00
-- url     : https://prove2.me/theorems/1af90c15-54ac-4253-95e4-8424ab65aebe
-- title:
--   Pad: size pad
-- statement:
--   The size of the pad of length 2^k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L49-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L49-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_PaddedDescent_size_pad

set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}

theorem CountKSatRate.Pad.size_pad (k : ℕ) : size (pad k) = 2 * 2 ^ k + 1 := by sorry
