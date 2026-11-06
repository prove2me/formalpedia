-- Prove2me | Theorems.Thm_ClauseBound_TopN_Cert_lamS_unary
-- name    : ClauseBound.TopN.Cert.lamS_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:27:08.009039+00:00
-- url     : https://prove2.me/theorems/ea6e65cd-76cd-4344-bad9-3ab8fdc9ee0d
-- title:
--   Cert: lam S unary
-- statement:
--   The label length of the rebalanced instance is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Cert.lean#L100-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Cert.lean#L100-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ClauseBound_TopN_Cert
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open PaddedDescent.F.Mark (MCtx Cl cls nProf adm markF placeE)
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem ClauseBound.TopN.Cert.lamS_unary {K g Ub P : α → ℕ} (hK : Unary K) (hg : Unary g) (hU : Unary Ub) (hP : Unary P) : Unary fun x => lamS (K x) (g x) (Ub x) (P x) := by sorry
