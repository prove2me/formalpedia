-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_tOf_unary
-- name    : Eight.SecCrossing_Cert.tOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:48:56.868615+00:00
-- url     : https://prove2.me/theorems/a053fde0-223b-4065-af84-f6ca3a9e609a
-- title:
--   Sec Crossing Cert: t Of unary
-- statement:
--   t = ⌈λ/3⌉ is given in unary, for λ in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L54-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L54-L55

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

theorem Eight.SecCrossing_Cert.tOf_unary {lam : α → ℕ} (hl : Unary lam) : Unary fun x => tOf (lam x) := by sorry
