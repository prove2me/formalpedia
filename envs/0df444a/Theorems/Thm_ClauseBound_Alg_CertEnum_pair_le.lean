-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertEnum_pair_le
-- name    : ClauseBound.Alg.CertEnum.pair_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:39.575384+00:00
-- url     : https://prove2.me/theorems/43e302b2-1766-40bc-b2b2-7e79b7296c86
-- title:
--   Cert Enum: pair le
-- statement:
--   The number of the chunk of two nodes below g is below g·g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L82-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertEnum.lean#L82-L87

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

theorem ClauseBound.Alg.CertEnum.pair_le {g a b : ℕ} (ha : a < g) (hb : b < g) : min a b * g + max a b ≤ g * g := by sorry
