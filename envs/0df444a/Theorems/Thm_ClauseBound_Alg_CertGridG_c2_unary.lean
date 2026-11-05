-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_c2_unary
-- name    : ClauseBound.Alg.CertGridG.c2_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:12:53.963467+00:00
-- url     : https://prove2.me/theorems/49dd38af-1c29-4fce-9861-3c4ab1beead3
-- title:
--   Cert Grid G: c2 unary
-- statement:
--   g(g − 1)/2 is given in unary if g is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L74-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L74-L76

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

theorem ClauseBound.Alg.CertGridG.c2_unary {g : α → ℕ} (hg : Unary g) : Unary fun x => c2 (g x) := by sorry
