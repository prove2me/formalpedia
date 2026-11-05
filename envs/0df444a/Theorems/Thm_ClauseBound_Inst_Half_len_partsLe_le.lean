-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_len_partsLe_le
-- name    : ClauseBound.Inst.Half.len_partsLe_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:35.381676+00:00
-- url     : https://prove2.me/theorems/d3d4642c-5131-4ecc-8590-ec7c0170dfeb
-- title:
--   Half: len parts Le le
-- statement:
--   The word of the list of the partitions of E into parts ≤ k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L287-L292
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L287-L292

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

theorem ClauseBound.Inst.Half.len_partsLe_le (E k : ℕ) : len (partsLe E k) ≤ p E * (7 * E + 4) + 2 := by sorry
