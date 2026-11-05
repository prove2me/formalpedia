-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_toNat_wOf_le
-- name    : ClauseBound.Inst.Half.toNat_wOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:52:57.87128+00:00
-- url     : https://prove2.me/theorems/e3c6ea9c-a269-476f-9f31-f2ca162e2624
-- title:
--   Half: to Nat w Of le
-- statement:
--   The Half construction uses the to Nat w Of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L90-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L90-L92

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

theorem ClauseBound.Inst.Half.toNat_wOf_le {h : ℕ} {s : ℤ} (hs : |s| ≤ 2 * h) (tr : Bool) {j : ℕ} (hj : j ≤ 2 * h) : (wOf tr h s j).toNat ≤ 4 * h := by sorry
