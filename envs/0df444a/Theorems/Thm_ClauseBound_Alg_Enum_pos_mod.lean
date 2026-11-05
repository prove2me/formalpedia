-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_pos_mod
-- name    : ClauseBound.Alg.Enum.pos_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:34:07.674319+00:00
-- url     : https://prove2.me/theorems/9d6b53ce-98b1-4d99-9802-117a4fc64894
-- title:
--   Enum: pos mod
-- statement:
--   The Enum construction uses the pos mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L86-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L86-L87

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
variable {g : ℕ}

theorem ClauseBound.Alg.Enum.pos_mod (p : Fin g × Fin g) : pos p % g = p.2.val := by sorry
