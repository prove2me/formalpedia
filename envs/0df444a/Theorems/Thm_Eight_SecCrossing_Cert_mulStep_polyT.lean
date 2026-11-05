-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_mulStep_polyT
-- name    : Eight.SecCrossing_Cert.mulStep_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:55:26.954864+00:00
-- url     : https://prove2.me/theorems/9c3a6f5a-3147-4204-a08e-6d5d89518fc5
-- title:
--   Sec Crossing Cert: mul Step poly T
-- statement:
--   One multiplication is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L100-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L100-L102

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

theorem Eight.SecCrossing_Cert.mulStep_polyT {r c : α → ℤ} {l : α → List ℤ} (hr : PolyT r) (hc : PolyT c) (hl : PolyT l) : PolyT fun x => mulStep (r x) (c x) (l x) := by sorry
