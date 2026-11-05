-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_divZ_polyT
-- name    : ClauseBound.Alg.CertLevel.divZ_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:29:08.660834+00:00
-- url     : https://prove2.me/theorems/8cbae4e6-627b-4b07-a221-b9d7cc49f79a
-- title:
--   Cert Level: div Z poly T
-- statement:
--   Division of an integer by a natural number is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L55-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L55-L62

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

theorem ClauseBound.Alg.CertLevel.divZ_polyT {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x / (b x : ℤ) := by sorry
