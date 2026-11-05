-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_longCap_polyT
-- name    : Eight.SecCrossing_Cert.longCap_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:55:44.474739+00:00
-- url     : https://prove2.me/theorems/a470f105-2e64-4e05-8076-e83e8f19dcbb
-- title:
--   Sec Crossing Cert: long Cap poly T
-- statement:
--   The number of bits of the factorization with θ = (Q, θ') is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L128-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L128-L129

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

theorem Eight.SecCrossing_Cert.longCap_polyT {tr : α → Bool} {t i : α → ℕ} (htr : PolyT tr) (ht : PolyT t) (hi : PolyT i) : PolyT fun x => longCap (tr x) (t x) (i x) := by sorry
