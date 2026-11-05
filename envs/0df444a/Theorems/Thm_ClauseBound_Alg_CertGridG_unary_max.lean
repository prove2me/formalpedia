-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_unary_max
-- name    : ClauseBound.Alg.CertGridG.unary_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:13:44.07802+00:00
-- url     : https://prove2.me/theorems/4f4e674c-4525-4699-a74b-7b96d488e98b
-- title:
--   Cert Grid G: unary max
-- statement:
--   The larger of two numbers given in unary is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L62-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L62-L63

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

theorem ClauseBound.Alg.CertGridG.unary_max {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => max (f x) (g x) := by sorry
