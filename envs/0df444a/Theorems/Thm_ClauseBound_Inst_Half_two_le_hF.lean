-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_two_le_hF
-- name    : ClauseBound.Inst.Half.two_le_hF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:11.2267+00:00
-- url     : https://prove2.me/theorems/07f480e5-b4d0-4667-a93d-b08b39125469
-- title:
--   Half: two le h F
-- statement:
--   `hF` is at least 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L163-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L163-L170

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

theorem ClauseBound.Inst.Half.two_le_hF (c₀ lam : ℕ) : 2 ≤ hF c₀ lam := by sorry
