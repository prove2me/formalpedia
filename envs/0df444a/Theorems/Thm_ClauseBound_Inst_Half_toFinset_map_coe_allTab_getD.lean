-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_toFinset_map_coe_allTab_getD
-- name    : ClauseBound.Inst.Half.toFinset_map_coe_allTab_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:41.251207+00:00
-- url     : https://prove2.me/theorems/e94e124f-f3d4-413d-8328-08cc9fd8935b
-- title:
--   Half: to Finset map coe all Tab get D
-- statement:
--   As multisets they are the monomials of weight E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L243-L246
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L243-L246

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.toFinset_map_coe_allTab_getD {W E : ℕ} (h : E ≤ W) :
    (((allTab W).getD E []).map fun L : List ℕ => (L : Multiset ℕ)).toFinset = ClauseBound.Boson.P E := by sorry
