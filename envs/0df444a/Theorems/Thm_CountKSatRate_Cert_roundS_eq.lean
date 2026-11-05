-- Prove2me | Theorems.Thm_CountKSatRate_Cert_roundS_eq
-- name    : CountKSatRate.Cert.roundS_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:17:39.909494+00:00
-- url     : https://prove2.me/theorems/c3234028-3d9f-42ab-848e-910e76f94046
-- title:
--   Cert: round S eq
-- statement:
--   `roundS` with its case distinctions written by eliminators.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Cert.lean#L44-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Cert.lean#L44-L50

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
import Theorems.Thm_Groundwork_PolyT_elim

set_option autoImplicit false
section
section
open CountKSatRate
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open WidthK (theta)
open CountKSatRate.Cert
variable {α σ : Type} [Enc α]
omit [Enc α]

theorem CountKSatRate.Cert.roundS_eq (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) :
    roundS step val st = st.1.head?.elim ([], st.2) fun s =>
      (step s).elim (st.1.tail, st.2 + val s) fun lh => (lh.1 :: lh.2 :: st.1.tail, st.2) := by sorry
