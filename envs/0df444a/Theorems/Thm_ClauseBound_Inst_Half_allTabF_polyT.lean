-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_allTabF_polyT
-- name    : ClauseBound.Inst.Half.allTabF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:41:06.494199+00:00
-- url     : https://prove2.me/theorems/08f8ce49-2955-4167-82a9-30e00cb84a28
-- title:
--   Half: all Tab F poly T
-- statement:
--   The table of all partitions of 0, …, W with the pad is polynomial-time in the pad and W in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L140-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L140-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.allTabF_polyT {pad : α → U} {W : α → ℕ} (hp : PolyT pad) (hW : Unary W) : PolyT fun x => allTabF (pad x) (W x) := by sorry
