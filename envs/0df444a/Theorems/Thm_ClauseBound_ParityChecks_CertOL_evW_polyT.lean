-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertOL_evW_polyT
-- name    : ClauseBound.ParityChecks.CertOL.evW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:43:39.16121+00:00
-- url     : https://prove2.me/theorems/ee17c371-592c-47c5-a9a1-ad64cbdc7609
-- title:
--   Cert OL: ev W poly T
-- statement:
--   One evaluation is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L114-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L114-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
variable (G : Given S) (k : ℕ) {pad : α → U} {i : α → Idx} {n Δ : α → ℕ} {q : α → Par} (hc : CU pad i n Δ q)
include G hc

theorem ClauseBound.ParityChecks.CertOL.evW_polyT {ws : α → List ℤ} {lo hi : α → List ℕ} {Ls : α → List Fml} (hws : PolyT ws) (hlo : PolyT lo) (hhi : PolyT hi) (hL : PolyT Ls) :
    PolyT fun x => evW S k (pad x) (i x) (n x) (Δ x) (q x) (ws x) (lo x) (hi x) (Ls x) := by sorry
