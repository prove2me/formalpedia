-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_wOf_polyT
-- name    : ClauseBound.Inst.Half.Cert.wOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:52.025979+00:00
-- url     : https://prove2.me/theorems/61aecd04-00a2-4a65-ac90-271915258ac3
-- title:
--   Cert: w Of poly T
-- statement:
--   The weight of τ in a pair (j, τ) is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L55-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L55-L57

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

theorem ClauseBound.Inst.Half.Cert.wOf_polyT {tr : α → Bool} {h j : α → ℕ} {s : α → ℤ} (ht : PolyT tr) (hh : PolyT h) (hs : PolyT s) (hj : PolyT j) :
    PolyT fun x => wOf (tr x) (h x) (s x) (j x) := by sorry
