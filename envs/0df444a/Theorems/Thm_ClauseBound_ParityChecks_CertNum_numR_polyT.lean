-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertNum_numR_polyT
-- name    : ClauseBound.ParityChecks.CertNum.numR_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:47.532144+00:00
-- url     : https://prove2.me/theorems/94ff03cf-4439-4813-80d2-591ddd250974
-- title:
--   Cert Num: num R poly T
-- statement:
--   The numerator of the term that sums over the checks (`Par.numR`), with 2 to the size of each
--   check, is polynomial-time, for e in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L97-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertNum.lean#L97-L100

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

theorem ClauseBound.ParityChecks.CertNum.numR_polyT {q : α → Par} (hq : QU q) {Ls : α → List Chk} {cur : α → Chk} {e : α → ℕ} (hL : PolyT Ls) (hc : PolyT cur) (he : Unary e) :
    PolyT fun x => (q x).numR (Ls x) (cur x) (e x) := by sorry
