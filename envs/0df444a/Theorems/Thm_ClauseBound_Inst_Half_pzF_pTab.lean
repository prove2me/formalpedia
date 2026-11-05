-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_pzF_pTab
-- name    : ClauseBound.Inst.Half.pzF_pTab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:00:58.131349+00:00
-- url     : https://prove2.me/theorems/c4756c08-2d42-44a5-bb7a-019fbfc9629b
-- title:
--   Half: pz F p Tab
-- statement:
--   The entry number E ≤ W, for an integer E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L134-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L134-L138

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

theorem ClauseBound.Inst.Half.pzF_pTab {W : ℕ} {E : ℤ} (h : E ≤ W) : pzF (pTab W) E = pz E := by sorry
