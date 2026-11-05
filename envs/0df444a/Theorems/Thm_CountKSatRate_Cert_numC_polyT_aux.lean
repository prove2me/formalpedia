-- Prove2me | Theorems.Thm_CountKSatRate_Cert_numC_polyT_aux
-- name    : CountKSatRate.Cert.numC_polyT_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:55.937817+00:00
-- url     : https://prove2.me/theorems/a5a3b631-7186-400d-b1b7-ad1ba6ec59ee
-- title:
--   Cert: num C poly T aux
-- statement:
--   The number of the padded input, with the decoded input d, the pad, the threshold τ and the value
--   function as arbitrary functions of a context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Cert.lean#L64-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Cert.lean#L64-L68

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
set_option autoImplicit false
section
section
open CountKSatRate
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open WidthK (theta)
open CountKSatRate.Cert
variable {α σ : Type} [Enc α]

theorem CountKSatRate.Cert.numC_polyT_aux (hW : StCertWalkS) (k : ℕ) {d : α → List Unit × Fml} {pad : α → U} {τ : α → ℕ} {val : α → CNode → ℕ} (hd : PolyT d)
    (hp : PolyT pad) (hτ : PolyT τ) (hv : PolyT fun q : α × CNode => val q.1 q.2) :
    PolyT fun p => bif hasNil (d p).2 then 0 else walkS k (pad p) (τ p) (val p) (rootC (d p)) := by sorry
