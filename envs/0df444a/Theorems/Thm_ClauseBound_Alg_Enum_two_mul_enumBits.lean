-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_two_mul_enumBits
-- name    : ClauseBound.Alg.Enum.two_mul_enumBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:31.472777+00:00
-- url     : https://prove2.me/theorems/01af84aa-1892-4478-b756-dc0a7372e4a9
-- title:
--   Enum: two mul enum Bits
-- statement:
--   The word of all labels has U/2 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L137-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L137-L146

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

theorem ClauseBound.Alg.Enum.two_mul_enumBits (hN : F.toP.Presents c N 0 0) : 2 * enumBits g F c = N.U := by sorry
