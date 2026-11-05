-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_enumLen_pos
-- name    : ClauseBound.Alg.Enum.enumLen_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:55.508112+00:00
-- url     : https://prove2.me/theorems/9878d022-7b37-464c-9b03-1a53bb43a456
-- title:
--   Enum: enum Len pos
-- statement:
--   The Enum construction uses the enum Len pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L132-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L132-L134

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

theorem ClauseBound.Alg.Enum.enumLen_pos (p : Fin g × Fin g) : enumLen g F c (pos p) = if p.1 < p.2 then F.cap c p.1 p.2 else 0 := by sorry
