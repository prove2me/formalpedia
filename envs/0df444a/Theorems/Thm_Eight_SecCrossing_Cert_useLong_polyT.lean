-- Prove2me | Theorems.Thm_Eight_SecCrossing_Cert_useLong_polyT
-- name    : Eight.SecCrossing_Cert.useLong_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:15:19.609759+00:00
-- url     : https://prove2.me/theorems/c4ded8b1-2b92-496a-baa6-586e68ec084e
-- title:
--   Sec Crossing Cert: use Long poly T
-- statement:
--   The choice between the two factorizations is polynomial-time, for λ in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L132-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Cert.lean#L132-L135

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

theorem Eight.SecCrossing_Cert.useLong_polyT {tr : α → Bool} {lam i : α → ℕ} (htr : PolyT tr) (hl : Unary lam) (hi : PolyT i) : PolyT fun x => useLong (tr x) (lam x) (i x) := by sorry
