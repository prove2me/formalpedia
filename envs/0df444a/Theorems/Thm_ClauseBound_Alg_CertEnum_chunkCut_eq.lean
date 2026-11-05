-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertEnum_chunkCut_eq
-- name    : ClauseBound.Alg.CertEnum.chunkCut_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:01.460035+00:00
-- url     : https://prove2.me/theorems/4f4c415b-c2ca-4880-9b25-88d637f1127a
-- title:
--   Cert Enum: chunk Cut eq
-- statement:
--   Below g·g the cut-off does nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L77-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L77-L79

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
omit [Enc C]

theorem ClauseBound.Alg.CertEnum.chunkCut_eq {g : ℕ} (F : FNet C) (c : C) {j : ℕ} (hj : j ≤ g * g) (w : List Bool) :
    chunkCut g F c j w = chunkAt (enumLen g F c) j w := by sorry
