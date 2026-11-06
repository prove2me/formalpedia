-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertOL_runF_polyT
-- name    : ClauseBound.ParityChecks.CertOL.runF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:11.416484+00:00
-- url     : https://prove2.me/theorems/331e14f1-4e08-4085-9029-8e41b5da6ab0
-- title:
--   Cert OL: run F poly T
-- statement:
--   The choice of all checks is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L176-L183
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L176-L183

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

theorem ClauseBound.ParityChecks.CertOL.runF_polyT {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => runF S k (pad x) (i x) (n x) (Δ x) (q x) (ψ x) := by sorry
