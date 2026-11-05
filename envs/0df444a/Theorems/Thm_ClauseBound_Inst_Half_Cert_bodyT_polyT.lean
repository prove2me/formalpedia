-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_bodyT_polyT
-- name    : ClauseBound.Inst.Half.Cert.bodyT_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:35.948513+00:00
-- url     : https://prove2.me/theorems/25b14628-a380-45d8-8705-e9ad192321e6
-- title:
--   Cert: body T poly T
-- statement:
--   The value at a pair (j, τ) is polynomial-time, for h and j in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L110-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L110-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.Cert.bodyT_polyT (Ht : StTopF) (Hb : StBotF) {pad : α → U} {tr top : α → Bool} {h j : α → ℕ} {s : α → ℤ} {T : α → PT} {a b : α → List Bool}
    {τ : α → List ℕ} (hp : PolyT pad) (htr : PolyT tr) (htop : PolyT top) (hh : Unary h) (hs : PolyT s) (hT : PolyT T) (ha : PolyT a) (hb : PolyT b)
    (hj : Unary j) (hτ : PolyT τ) :
    PolyT fun x => bodyT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (j x) (τ x) := by sorry
