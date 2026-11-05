-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_pTab_getD
-- name    : ClauseBound.Inst.Half.pTab_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:00:02.431036+00:00
-- url     : https://prove2.me/theorems/9cca32c0-9ea9-4ff7-963f-9d38ae0e3720
-- title:
--   Half: p Tab get D
-- statement:
--   The entry number i ≤ W of the table is p(i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L130-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L130-L131

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

theorem ClauseBound.Inst.Half.pTab_getD (W i : ℕ) (h : i ≤ W) : (pTab W).getD i 0 = Partitions.p i := by sorry
