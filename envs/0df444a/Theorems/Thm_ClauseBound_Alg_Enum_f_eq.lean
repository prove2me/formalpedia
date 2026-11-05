-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_f_eq
-- name    : ClauseBound.Alg.Enum.f_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:56.783386+00:00
-- url     : https://prove2.me/theorems/0880493c-ed48-4440-965b-b9c2070b417b
-- title:
--   Enum: f eq
-- statement:
--   The Enum construction uses the f eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L119-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L119-L121

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

theorem ClauseBound.Alg.Enum.f_eq (hN : F.toP.Presents c N 0 0) (a b : Fin g) (z θ : List Bool) (hab : a ≠ b) (hz : z.length = F.n c a)
    (hθ : θ.length = F.cap c a b) : F.f (c, ((a.val, b.val), (z, θ))) = N.f a b z θ := by sorry
