-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertEnum_enumLen_unary
-- name    : ClauseBound.Alg.CertEnum.enumLen_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:36:16.838044+00:00
-- url     : https://prove2.me/theorems/21b2c795-9a41-41db-91f1-924291935238
-- title:
--   Cert Enum: enum Len unary
-- statement:
--   The length of a chunk is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L44-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L44-L58

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

theorem ClauseBound.Alg.CertEnum.enumLen_unary (hF : FKeeps F) {g j : α → ℕ} {c : α → C} (hg : PolyT g) (hc : PolyT c) (hj : PolyT j) :
    Unary fun t => enumLen (g t) F (c t) (j t) := by sorry
