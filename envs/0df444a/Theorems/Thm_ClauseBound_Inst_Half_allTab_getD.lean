-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_allTab_getD
-- name    : ClauseBound.Inst.Half.allTab_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:52:19.962744+00:00
-- url     : https://prove2.me/theorems/ef4b413a-43bc-4cad-905b-d5815c43c472
-- title:
--   Half: all Tab get D
-- statement:
--   The entry number E ≤ W of the table is the list of the partitions of E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L225-L226
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L225-L226

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

theorem ClauseBound.Inst.Half.allTab_getD {W E : ℕ} (h : E ≤ W) : (allTab W).getD E [] = partsOf E := by sorry
