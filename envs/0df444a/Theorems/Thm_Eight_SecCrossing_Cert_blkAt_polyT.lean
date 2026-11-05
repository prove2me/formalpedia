-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_blkAt_polyT
-- name    : Eight.SecCrossing_Cert.blkAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:27:56.864731+00:00
-- url     : https://prove2.me/theorems/25981d4d-5b8f-4472-a525-40f52dbe4714
-- title:
--   Sec Crossing Cert: blk At poly T
-- statement:
--   Three bits of a list from a position on.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L60-L61

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

theorem Eight.SecCrossing_Cert.blkAt_polyT {w : α → List Bool} {j : α → ℕ} (hw : PolyT w) (hj : PolyT j) : PolyT fun x => blkAt (w x) (j x) := by sorry
