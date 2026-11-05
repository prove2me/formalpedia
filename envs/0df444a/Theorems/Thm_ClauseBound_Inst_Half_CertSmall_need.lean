-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_CertSmall_need
-- name    : ClauseBound.Inst.Half.CertSmall.need
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:41.963837+00:00
-- url     : https://prove2.me/theorems/8fc20d87-5957-47ed-953e-620612874522
-- title:
--   Cert Small: need
-- statement:
--   The exponent c·λ of the pad is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L56-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.CertSmall
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.CertSmall.need (c₀ c : ℕ) : Unary fun p : U × U => (halfF c₀ c).need p.1.length p.2.length := by sorry
