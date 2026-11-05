-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_topAt_polyT
-- name    : Eight.SecCrossing_Cert.topAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:55:51.074575+00:00
-- url     : https://prove2.me/theorems/04687921-4b74-4a9b-8b8a-df4f038b13f8
-- title:
--   Sec Crossing Cert: top At poly T
-- statement:
--   The factor of the block number s in the first function is polynomial-time, for s in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L150-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L150-L159

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

theorem Eight.SecCrossing_Cert.topAt_polyT {tr : α → Bool} {Q w a b : α → List Bool} {s : α → ℕ} (htr : PolyT tr) (hQ : PolyT Q) (hw : PolyT w) (ha : PolyT a) (hb : PolyT b)
    (hs : Unary s) : PolyT fun x => topAt (tr x) (Q x) (w x) (a x) (b x) (s x) := by sorry
