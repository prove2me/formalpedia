-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_sum_range_eq_sum_pos
-- name    : ClauseBound.Alg.Enum.sum_range_eq_sum_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:56.906452+00:00
-- url     : https://prove2.me/theorems/f791e106-e6fe-45d0-84e5-2dff83a6520e
-- title:
--   Enum: sum range eq sum pos
-- statement:
--   A sum over all numbers below g·g is a sum over all pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L101-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L101-L105

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

theorem ClauseBound.Alg.Enum.sum_range_eq_sum_pos (G : ℕ → ℕ) : ∑ j ∈ range (g * g), G j = ∑ p : Fin g × Fin g, G (pos p) := by sorry
