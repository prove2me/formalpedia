-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_roundF_polyT
-- name    : ClauseBound.Inst.Half.roundF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:42:02.338112+00:00
-- url     : https://prove2.me/theorems/f041d3e7-3100-465c-b9a5-15119059622f
-- title:
--   Half: round F poly T
-- statement:
--   One round with the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L131-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L131-L136

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

theorem ClauseBound.Inst.Half.roundF_polyT {pad : α → U} {W k : α → ℕ} {old : α → PT} (hp : PolyT pad) (hW : Unary W) (hk : PolyT k) (ho : PolyT old) :
    PolyT fun x => roundF (pad x) (W x) (k x) (old x) := by sorry
