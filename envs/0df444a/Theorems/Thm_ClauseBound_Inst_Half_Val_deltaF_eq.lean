-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Val_deltaF_eq
-- name    : ClauseBound.Inst.Half.Val.deltaF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:51:24.759375+00:00
-- url     : https://prove2.me/theorems/7947ad95-0874-4e74-9411-5360d70a02f5
-- title:
--   Val: delta F eq
-- statement:
--   The number of all partitions of 0, …, 4h, as a sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L60-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Val

theorem ClauseBound.Inst.Half.Val.deltaF_eq (h : ℕ) : deltaF h = ∑ E ∈ range (4 * h + 1), Partitions.p E := by sorry
