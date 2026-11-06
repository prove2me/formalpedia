-- Prove2me | Theorems.Thm_CountKSatRate_Cert_bruteN_polyT_aux
-- name    : CountKSatRate.Cert.bruteN_polyT_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:14:12.278263+00:00
-- url     : https://prove2.me/theorems/f89daeb6-7c96-4362-9500-e56dc430a8b8
-- title:
--   Cert: brute N poly T aux
-- statement:
--   The number `bruteN k` with the decoded input d and the pad as arbitrary functions of a context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Cert.lean#L71-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Cert.lean#L71-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_InOut
import Definitions.Def_PaddedDescent_F_CertA
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_PaddedDescent_F_CertSide
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_CountKSatRate_Cert
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CountKSatRate
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open WidthK (theta)
open CountKSatRate.Cert
variable {α σ : Type} [Enc α]

theorem CountKSatRate.Cert.bruteN_polyT_aux {d : α → List Unit × Fml} {pad : α → U} (hd : PolyT d) (hp : PolyT pad) :
    PolyT fun p => ((rng (pad p) (2 ^ (d p).1.length)).filter fun y => satAt (d p).2 y).length := by sorry
