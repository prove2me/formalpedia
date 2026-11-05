-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_partT_polyT
-- name    : ClauseBound.Inst.Half.Cert.partT_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:16.998416+00:00
-- url     : https://prove2.me/theorems/664ede86-ba82-4ee6-ba6b-32c14a9c2741
-- title:
--   Cert: part T poly T
-- statement:
--   One of the two functions of a factorization, with its arguments apart, is polynomial-time, for h
--   in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L126-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L126-L136

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

theorem ClauseBound.Inst.Half.Cert.partT_polyT (Ht : StTopF) (Hb : StBotF) {pad : α → U} {tr top : α → Bool} {h : α → ℕ} {s : α → ℤ} {T : α → PT} {a b θ : α → List Bool}
    (hp : PolyT pad) (htr : PolyT tr) (htop : PolyT top) (hh : Unary h) (hs : PolyT s) (hT : PolyT T) (ha : PolyT a) (hb : PolyT b) (hθ : PolyT θ) :
    PolyT fun x => partT (pad x) (tr x) (top x) (h x) (s x) (T x) (a x) (b x) (θ x) := by sorry
