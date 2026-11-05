-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_planAtO_polyT
-- name    : ClauseBound.ParityChecks.CertTopOL.planAtO_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:20:10.950802+00:00
-- url     : https://prove2.me/theorems/5c8795fd-fbb5-47c5-9a79-08f20bdf2e83
-- title:
--   Cert Top OL: plan At O poly T
-- statement:
--   The plan, jointly in n and s in unary and the index.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L135-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L135-L159

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem ClauseBound.ParityChecks.CertTopOL.planAtO_polyT (hP : S.Poly) (c n₀ k : ℕ) {n s : α → ℕ} {i : α → Idx} (hn : Unary n) (hi : PolyT i) (hs : Unary s) :
    PolyT fun x => planAtO S c n₀ k (n x) (i x) (s x) := by sorry
