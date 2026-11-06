-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_Nof_unary
-- name    : ClauseBound.Alg.CertGridG.Nof_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:17:36.543566+00:00
-- url     : https://prove2.me/theorems/4a07e3ac-3476-413e-bfdf-81a0d156b13a
-- title:
--   Cert Grid G: Nof unary
-- statement:
--   N = (pd)²λ is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L264-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L264-L265

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
variable {s : α → Step} (hs : PolyT s)
include hs

theorem ClauseBound.Alg.CertGridG.Nof_unary {lam : α → ℕ} (hl : Unary lam) : Unary fun x => Nof (s x) (lam x) := by sorry
