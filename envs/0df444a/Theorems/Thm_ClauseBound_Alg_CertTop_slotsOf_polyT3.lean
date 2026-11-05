-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_slotsOf_polyT3
-- name    : ClauseBound.Alg.CertTop.slotsOf_polyT3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:38:47.113803+00:00
-- url     : https://prove2.me/theorems/d3fefc7a-3efb-46b8-99f1-bc29f0ea5e81
-- title:
--   Cert Top: slots Of poly T3
-- statement:
--   The list of the slots of a formula, jointly in k, in unary, and the formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L45-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_CertCount
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_CountKSat_Poly
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ClauseBound_Alg_CertTop
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent PaddedDescent.F ClauseBound.Alg.CertCount CountKSat CountKSat.Poly
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.CertTop.slotsOf_polyT3 {k : α → ℕ} {φ : α → Fml} (hk : Unary k) (hφ : PolyT φ) : PolyT fun x => slotsOf (k x) (φ x) := by sorry
