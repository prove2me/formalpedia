-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertEnum_enumF_polyT
-- name    : ClauseBound.Alg.CertEnum.enumF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:53.297389+00:00
-- url     : https://prove2.me/theorems/d9050f5c-41fe-4605-8d71-705d60c2dde0
-- title:
--   Cert Enum: enum F poly T
-- statement:
--   Evaluation by enumeration is polynomial-time in the pad, g in unary and the context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L125-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L125-L174

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

theorem ClauseBound.Alg.CertEnum.enumF_polyT (hF : FKeeps F) {pad : α → U} {g : α → ℕ} {c : α → C} (hp : PolyT pad) (hg : Unary g) (hc : PolyT c) :
    PolyT fun t => enumF (pad t) (g t) F (c t) := by sorry
