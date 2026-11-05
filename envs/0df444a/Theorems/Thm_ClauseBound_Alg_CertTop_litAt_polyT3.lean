-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertTop_litAt_polyT3
-- name    : ClauseBound.Alg.CertTop.litAt_polyT3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:38:22.415191+00:00
-- url     : https://prove2.me/theorems/c7e09976-7e38-4c0a-84bc-6de5b0eec471
-- title:
--   Cert Top: lit At poly T3
-- statement:
--   The literal at a slot, jointly in k, the formula and the slot.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertTop.lean#L35-L37

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

theorem ClauseBound.Alg.CertTop.litAt_polyT3 {k : α → ℕ} {φ : α → Fml} {i : α → ℕ} (hk : PolyT k) (hφ : PolyT φ) (hi : PolyT i) :
    PolyT fun x => litAt (k x) (φ x) (i x) := by sorry
