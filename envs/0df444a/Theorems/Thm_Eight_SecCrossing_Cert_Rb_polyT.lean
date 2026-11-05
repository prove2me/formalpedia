-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_Rb_polyT
-- name    : Eight.SecCrossing_Cert.Rb_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:15:30.361299+00:00
-- url     : https://prove2.me/theorems/a8db159f-eb3b-482c-9261-d1431d0d5c58
-- title:
--   Sec Crossing Cert: Rb poly T
-- statement:
--   R is a table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L73-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L73-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open Eight.SecCrossing_Cert
variable {α : Type} [Enc α]

theorem Eight.SecCrossing_Cert.Rb_polyT {a b c d : α → Block} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) (hd : PolyT d) : PolyT fun x => Rb (a x) (b x) (c x) (d x) := by sorry
