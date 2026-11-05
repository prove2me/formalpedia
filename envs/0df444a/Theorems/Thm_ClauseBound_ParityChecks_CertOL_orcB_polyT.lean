-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertOL_orcB_polyT
-- name    : ClauseBound.ParityChecks.CertOL.orcB_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:22:07.754524+00:00
-- url     : https://prove2.me/theorems/3f631b36-7d16-4a6c-a246-80102ec0c339
-- title:
--   Cert OL: orc B poly T
-- statement:
--   The second of the two functions that the choice of the checks asks is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L142-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L142-L150

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

theorem ClauseBound.ParityChecks.CertOL.orcB_polyT {ψ : α → Fml} {Ls : α → List Chk} {cur : α → Chk} {e j : α → ℕ} (hψ : PolyT ψ) (hL : PolyT Ls) (hcur : PolyT cur) (he : PolyT e) (hj : PolyT j) :
    PolyT fun x => orcB S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) (Ls x) (cur x) (e x) (j x) := by sorry
