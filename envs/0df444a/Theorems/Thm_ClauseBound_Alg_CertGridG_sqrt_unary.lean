-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_sqrt_unary
-- name    : ClauseBound.Alg.CertGridG.sqrt_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:15:38.399893+00:00
-- url     : https://prove2.me/theorems/3d674cb9-c018-4070-b4ef-b49d79665d82
-- title:
--   Cert Grid G: sqrt unary
-- statement:
--   The square root of a number given in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L208-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L208-L209

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

theorem ClauseBound.Alg.CertGridG.sqrt_unary {f : α → ℕ} (hf : Unary f) : Unary fun x => Nat.sqrt (f x) := by sorry
