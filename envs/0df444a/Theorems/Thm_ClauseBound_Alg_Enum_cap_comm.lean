-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_cap_comm
-- name    : ClauseBound.Alg.Enum.cap_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:34:09.496037+00:00
-- url     : https://prove2.me/theorems/1edde17e-1758-4ad1-9cf1-a8d9e732b8a1
-- title:
--   Enum: cap comm
-- statement:
--   The two lengths given for the labels of a pair agree.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L124-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L124-L130

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}

theorem ClauseBound.Alg.Enum.cap_comm (hN : F.toP.Presents c N 0 0) (a b : Fin g) (hab : a ≠ b) : F.cap c a b = F.cap c b a := by sorry
