-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_CertSmall_bits
-- name    : ClauseBound.Inst.Half.CertSmall.bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:32.439283+00:00
-- url     : https://prove2.me/theorems/fef128d0-27fd-46f6-b726-40cdcbd71fba
-- title:
--   Cert Small: bits
-- statement:
--   The bound (2λ)^c for the number of bits of the values is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfSmall.lean#L60-L61

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

theorem ClauseBound.Inst.Half.CertSmall.bits (c₀ c : ℕ) : Unary fun p : U × U => (halfF c₀ c).bits p.1.length p.2.length := by sorry
