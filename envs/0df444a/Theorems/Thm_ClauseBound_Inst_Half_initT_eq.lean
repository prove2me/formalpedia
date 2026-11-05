-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_initT_eq
-- name    : ClauseBound.Inst.Half.initT_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:00:46.478407+00:00
-- url     : https://prove2.me/theorems/ce7d5825-b741-4239-b336-6f435f81fef0
-- title:
--   Half: init T eq
-- statement:
--   Before the first round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L194-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L194-L196

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.initT_eq (W : ℕ) : initT W = tabK W 0 := by sorry
