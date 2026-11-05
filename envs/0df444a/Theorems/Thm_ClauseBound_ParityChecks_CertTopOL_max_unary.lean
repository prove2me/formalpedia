-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_max_unary
-- name    : ClauseBound.ParityChecks.CertTopOL.max_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:58.709386+00:00
-- url     : https://prove2.me/theorems/20d1bf03-cd13-4783-9cce-bc7db98e25b0
-- title:
--   Cert Top OL: max unary
-- statement:
--   The Cert Top OL construction uses the max unary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L57-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L57-L58

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

theorem ClauseBound.ParityChecks.CertTopOL.max_unary {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => max (f x) (g x) := by sorry
