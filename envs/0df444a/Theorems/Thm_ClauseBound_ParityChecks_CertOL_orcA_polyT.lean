-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertOL_orcA_polyT
-- name    : ClauseBound.ParityChecks.CertOL.orcA_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:22:38.064705+00:00
-- url     : https://prove2.me/theorems/b0d91a1c-9dbe-4847-85d9-7c4f7ac56e1e
-- title:
--   Cert OL: orc A poly T
-- statement:
--   The first of the two functions that the choice of the checks asks is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L132-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L132-L139

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

theorem ClauseBound.ParityChecks.CertOL.orcA_polyT {ψ : α → Fml} {Ls : α → List Chk} (hψ : PolyT ψ) (hL : PolyT Ls) :
    PolyT fun x => orcA S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) (Ls x) := by sorry
