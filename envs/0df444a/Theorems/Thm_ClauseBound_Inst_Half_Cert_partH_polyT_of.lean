-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Cert_partH_polyT_of
-- name    : ClauseBound.Inst.Half.Cert.partH_polyT_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:01.579724+00:00
-- url     : https://prove2.me/theorems/4c6f0a87-cb60-40ec-8cfd-42279065b2e2
-- title:
--   Cert: part H poly T of
-- statement:
--   The two functions of a factorization are polynomial-time in the query, given the certificates of
--   the entries of the matrices.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L140-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalf.lean#L140-L145

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

theorem ClauseBound.Inst.Half.Cert.partH_polyT_of (Ht : StTopF) (Hb : StBotF) (c₀ : ℕ) (top : Bool) : PolyT (partH c₀ top) := by sorry
