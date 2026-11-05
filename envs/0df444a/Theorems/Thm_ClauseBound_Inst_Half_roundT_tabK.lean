-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_roundT_tabK
-- name    : ClauseBound.Inst.Half.roundT_tabK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:34.211547+00:00
-- url     : https://prove2.me/theorems/11c54848-b4de-4d6b-b851-c3d88179564e
-- title:
--   Half: round T tab K
-- statement:
--   Round k + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L214-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L214-L214

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

theorem ClauseBound.Inst.Half.roundT_tabK (W k : ℕ) : roundT W (k + 1) (tabK W k) = tabK W (k + 1) := by sorry
