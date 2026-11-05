-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_W_eq
-- name    : ClauseBound.Alg.Enum.W_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:46.837046+00:00
-- url     : https://prove2.me/theorems/919da251-3c4e-4f43-b4b5-abfa5146028a
-- title:
--   Enum: W eq
-- statement:
--   The Enum construction uses the W eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L115-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L115-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}

theorem ClauseBound.Alg.Enum.W_eq (hN : F.toP.Presents c N 0 0) (a : Fin g) (z : List Bool) (hz : z.length = F.n c a) :
    F.W (c, (a.val, z)) = N.W a z := by sorry
