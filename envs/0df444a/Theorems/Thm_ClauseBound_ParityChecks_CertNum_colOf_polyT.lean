-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_colOf_polyT
-- name    : ClauseBound.ParityChecks.CertNum.colOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:28:37.647544+00:00
-- url     : https://prove2.me/theorems/8cbc0973-8f6d-4b45-9c82-dfdf354494ad
-- title:
--   Cert Num: col Of poly T
-- statement:
--   The number of checks among Ls and cur that contain the clause x is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L32-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L32-L35

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

theorem ClauseBound.ParityChecks.CertNum.colOf_polyT {Ls : α → List Chk} {cur : α → Chk} {x : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (hx : PolyT x) :
    PolyT fun a => Par.colOf (Ls a) (cur a) (x a) := by sorry
