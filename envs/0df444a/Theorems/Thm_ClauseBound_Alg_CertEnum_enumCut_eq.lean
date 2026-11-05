-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertEnum_enumCut_eq
-- name    : ClauseBound.Alg.CertEnum.enumCut_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:28.258193+00:00
-- url     : https://prove2.me/theorems/dfb14dbc-f042-4012-ada0-ed01117acb08
-- title:
--   Cert Enum: enum Cut eq
-- statement:
--   The cut-off does not change the value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L113-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L113-L122

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

theorem ClauseBound.Alg.CertEnum.enumCut_eq (pad : U) (g : ℕ) (F : FNet C) (c : C) : enumCut pad g F c = enumF pad g F c := by sorry
