-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_capSum_unary
-- name    : ClauseBound.Alg.CertGridG.capSum_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:00:54.548963+00:00
-- url     : https://prove2.me/theorems/6d312448-1dca-43e3-9a40-687efda7e548
-- title:
--   Cert Grid G: cap Sum unary
-- statement:
--   The largest sum of the two numbers of bits of a piece is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L409-L411
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L409-L411

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
variable {P : PiecesF} (K : P.Keeps)
include K

theorem ClauseBound.Alg.CertGridG.capSum_unary {h lam : α → ℕ} (hh : Unary h) (hl : Unary lam) : Unary fun x => capSum P (h x) (lam x) := by sorry
