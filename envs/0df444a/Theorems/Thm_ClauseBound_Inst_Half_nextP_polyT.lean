-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_nextP_polyT
-- name    : ClauseBound.Inst.Half.nextP_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:39:45.263198+00:00
-- url     : https://prove2.me/theorems/009d963c-c442-4eff-b454-242e4d47083c
-- title:
--   Half: next P poly T
-- statement:
--   The next entry of the table of numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L31-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L31-L43

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

theorem ClauseBound.Inst.Half.nextP_polyT {T : α → List ℕ} (hT : PolyT T) : PolyT fun x => nextP (T x) := by sorry
