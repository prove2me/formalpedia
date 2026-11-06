-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_oneT_polyT
-- name    : ClauseBound.Inst.Half.oneT_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:17:06.646274+00:00
-- url     : https://prove2.me/theorems/3a99f843-d2f4-42f5-b07c-83149b47423e
-- title:
--   Half: one T poly T
-- statement:
--   The table of the identity.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L66-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L66-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfTab
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.oneT_polyT {flat : α → List (List ℕ)} (hf : PolyT flat) : PolyT fun x => oneT (flat x) := by sorry
