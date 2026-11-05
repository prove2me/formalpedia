-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertEnum_chunkCut_polyT
-- name    : ClauseBound.Alg.CertEnum.chunkCut_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:23.178965+00:00
-- url     : https://prove2.me/theorems/8ba4d183-7424-4f8a-ba72-094404e15290
-- title:
--   Cert Enum: chunk Cut poly T
-- statement:
--   A chunk, cut off, is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L90-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L90-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertEnum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertEnum
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.CertNet
variable {α : Type} [Enc α] {C : Type} [Enc C] {F : FNet C}

theorem ClauseBound.Alg.CertEnum.chunkCut_polyT (hF : FKeeps F) {g j : α → ℕ} {c : α → C} {w : α → List Bool} (hg : Unary g) (hc : PolyT c) (hj : PolyT j)
    (hw : PolyT w) : PolyT fun t => chunkCut (g t) F (c t) (j t) (w t) := by sorry
