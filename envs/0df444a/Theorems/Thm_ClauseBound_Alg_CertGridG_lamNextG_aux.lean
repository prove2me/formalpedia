-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_lamNextG_aux
-- name    : ClauseBound.Alg.CertGridG.lamNextG_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:50.965968+00:00
-- url     : https://prove2.me/theorems/92db21b3-50fd-451a-a1b1-c841c5cc5001
-- title:
--   Cert Grid G: lam Next G aux
-- statement:
--   The formula of the label length one level down, for any numbers given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L279-L283
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L279-L283

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

theorem ClauseBound.Alg.CertGridG.lamNextG_aux (m : ℕ) {D ub p d lam K : α → ℕ} (h1 : Unary D) (h2 : Unary ub) (h3 : Unary p) (h4 : Unary d) (h5 : Unary lam) (h6 : Unary K) :
    Unary fun x => (D x * ub x + 3 * p x ^ 2 * (d x ^ 2 * (m * lam x))) / (D x * K x ^ 2) + 1 := by sorry
