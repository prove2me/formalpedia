-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_pos_div
-- name    : ClauseBound.Alg.Enum.pos_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:33:41.468991+00:00
-- url     : https://prove2.me/theorems/0cf65d2a-6c73-4a31-af7a-8eb10dc78ace
-- title:
--   Enum: pos div
-- statement:
--   The Enum construction uses the pos div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L82-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L82-L84

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

theorem ClauseBound.Alg.Enum.pos_div (p : Fin g × Fin g) : pos p / g = p.1.val := by sorry
