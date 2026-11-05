-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_wOf_le
-- name    : ClauseBound.Inst.Half.wOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:06.780754+00:00
-- url     : https://prove2.me/theorems/fcf210b5-02ff-41f7-9859-036b95b2bd4b
-- title:
--   Half: w Of le
-- statement:
--   The weight of τ in a pair (j, τ) with j ≤ 2h is at most 4h if |s| ≤ 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L86-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L86-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs

theorem ClauseBound.Inst.Half.wOf_le {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) {j : ℕ} (hj : j ≤ 2 * h) : wOf tr h s j ≤ 4 * h := by sorry
