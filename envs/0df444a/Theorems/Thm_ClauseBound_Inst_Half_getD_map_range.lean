-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_getD_map_range
-- name    : ClauseBound.Inst.Half.getD_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:53:26.596601+00:00
-- url     : https://prove2.me/theorems/8733eb2b-0c82-42ac-96b6-d488c2c33cfd
-- title:
--   Half: get D map range
-- statement:
--   The entry number i of the list f 0, …, f (n − 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L97-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L97-L98

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

theorem ClauseBound.Inst.Half.getD_map_range {γ : Type} (f : ℕ → γ) (d : γ) {n i : ℕ} (h : i < n) : ((List.range n).map f).getD i d = f i := by sorry
