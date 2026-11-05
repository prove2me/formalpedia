-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertEnum_enumBits_unary
-- name    : ClauseBound.Alg.CertEnum.enumBits_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:57.815225+00:00
-- url     : https://prove2.me/theorems/53f1d5ce-f89a-4d1e-bf75-68077f046e01
-- title:
--   Cert Enum: enum Bits unary
-- statement:
--   The number of bits of the word of all labels is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L61-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L61-L67

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

theorem ClauseBound.Alg.CertEnum.enumBits_unary (hF : FKeeps F) {g : α → ℕ} {c : α → C} (hg : Unary g) (hc : PolyT c) :
    Unary fun t => enumBits (g t) F (c t) := by sorry
