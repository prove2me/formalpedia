-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_sqrt_polyT
-- name    : ClauseBound.Alg.CertLevel.sqrt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:03:16.531804+00:00
-- url     : https://prove2.me/theorems/f7869409-8c17-4bd9-aa19-9ab611fcfae6
-- title:
--   Cert Level: sqrt poly T
-- statement:
--   The square root of a number given in unary is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L288-L291
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L288-L291

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.sqrt_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => Nat.sqrt (n x) := by sorry
