-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_CertSmall_cap
-- name    : ClauseBound.Inst.Half.CertSmall.cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:44:29.041006+00:00
-- url     : https://prove2.me/theorems/c7d37a09-2421-4443-ab37-325cd1c7fe33
-- title:
--   Cert Small: cap
-- statement:
--   The number of bits of a factorization is given in unary; the number i of the piece is in binary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L45-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L45-L53

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

theorem ClauseBound.Inst.Half.CertSmall.cap (c₀ c : ℕ) : Unary fun p : Bool × U × U × ℕ => (halfF c₀ c).cap p.1 p.2.1.length p.2.2.1.length p.2.2.2 := by sorry
