-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_allTabF_eq
-- name    : ClauseBound.Inst.Half.allTabF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:33.246372+00:00
-- url     : https://prove2.me/theorems/6a6db7d7-d82a-40a2-ab0e-48f2b6de3558
-- title:
--   Half: all Tab F eq
-- statement:
--   With a pad of length at least (7W + 10)·Σ_{E ≤ W} p(E) no cut-off is active.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L342-L354
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L342-L354

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.allTabF_eq {pad : U} {W : ℕ} (hp : (7 * W + 10) * ∑ E ∈ range (W + 1), p E ≤ pad.length) : allTabF pad W = allTab W := by sorry
