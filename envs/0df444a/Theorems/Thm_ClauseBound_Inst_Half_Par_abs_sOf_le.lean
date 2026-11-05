-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Par_abs_sOf_le
-- name    : ClauseBound.Inst.Half.Par.abs_sOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:52:15.956936+00:00
-- url     : https://prove2.me/theorems/1bc2d896-4e0b-4164-9a93-73744e05c9af
-- title:
--   Par: abs s Of le
-- statement:
--   |s| ≤ 2h for the number s of a piece.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPar.lean#L33-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPar.lean#L33-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Inst_HalfPar
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Part ClauseBound.Inst.Rec
open ClauseBound.Inst.Half.Par

theorem ClauseBound.Inst.Half.Par.abs_sOf_le (h i : ℕ) : |sOf h i| ≤ 2 * (h : ℤ) := by sorry
