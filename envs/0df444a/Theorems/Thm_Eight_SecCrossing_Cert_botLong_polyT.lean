-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_botLong_polyT
-- name    : Eight.SecCrossing_Cert.botLong_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:56:04.148566+00:00
-- url     : https://prove2.me/theorems/bab542f3-af5e-46f5-bab2-64be869541a0
-- title:
--   Sec Crossing Cert: bot Long poly T
-- statement:
--   The second function of the factorization with θ = (Q, θ') is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L194-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L194-L198

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_MulOut
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_Eight_SecCrossing_Cert
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA
open Eight.SecCrossing_Cert
variable {α : Type} [Enc α]

theorem Eight.SecCrossing_Cert.botLong_polyT : PolyT fun q : Arg =>
    prodL (tOf q.2.2.1.length) (botAt q.1 (q.2.2.2.2.take (tOf q.2.2.1.length)) (q.2.2.2.2.drop (tOf q.2.2.1.length)) q.2.2.1 q.2.2.2.1) := by sorry
