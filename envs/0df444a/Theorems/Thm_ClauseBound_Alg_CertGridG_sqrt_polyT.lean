-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_sqrt_polyT
-- name    : ClauseBound.Alg.CertGridG.sqrt_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:14:42.598427+00:00
-- url     : https://prove2.me/theorems/4c065fd2-95be-4af0-ab28-8e14d8e9b51c
-- title:
--   Cert Grid G: sqrt poly T
-- statement:
--   The square root is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L191-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L191-L205

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

theorem ClauseBound.Alg.CertGridG.sqrt_polyT {f : α → ℕ} (hf : PolyT f) : PolyT fun x => Nat.sqrt (f x) := by sorry
