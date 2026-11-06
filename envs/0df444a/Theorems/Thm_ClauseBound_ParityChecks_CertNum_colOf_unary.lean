-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_colOf_unary
-- name    : ClauseBound.ParityChecks.CertNum.colOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:28:24.299505+00:00
-- url     : https://prove2.me/theorems/d738df63-00f9-4c17-8cef-35f9ed4969f9
-- title:
--   Cert Num: col Of unary
-- statement:
--   It is given in unary: it is at most the number of the checks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L38-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_ClauseBound_ParityChecks_CertNum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertNum
open Groundwork PaddedDescent.F ClauseBound.Alg.CertGridG ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertNum.colOf_unary {Ls : α → List Chk} {cur : α → Chk} {x : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (hx : PolyT x) :
    Unary fun a => Par.colOf (Ls a) (cur a) (x a) := by sorry
