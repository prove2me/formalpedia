-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_mulOut_polyT
-- name    : Eight.SecCrossing_Cert.mulOut_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:55:24.250202+00:00
-- url     : https://prove2.me/theorems/43d86418-1eea-4da1-ae6d-f791fc01c121
-- title:
--   Sec Crossing Cert: mul Out poly T
-- statement:
--   «multiplying them out one at a time takes time poly(λ)»: the paper's program is polynomial-time.
--   It is a loop of t rounds; a loop is polynomial-time if each round is and the words of all the states
--   that occur have polynomial length
--   (Groundwork.PolyT.foldl), which is len_mulUpTo_le.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L108-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L108-L117

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

theorem Eight.SecCrossing_Cert.mulOut_polyT : PolyT mulOut := by sorry
