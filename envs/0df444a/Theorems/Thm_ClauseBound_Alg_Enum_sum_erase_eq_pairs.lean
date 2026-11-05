-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_sum_erase_eq_pairs
-- name    : ClauseBound.Alg.Enum.sum_erase_eq_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:03.240905+00:00
-- url     : https://prove2.me/theorems/1aa0db7b-842e-40be-9d99-2fb6b8762e88
-- title:
--   Enum: sum erase eq pairs
-- statement:
--   A sum over ordered pairs of distinct nodes, regrouped by unordered pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L59-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L59-L69

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
variable {J σ τ : Type} [Fintype J] [LinearOrder J]

theorem ClauseBound.Alg.Enum.sum_erase_eq_pairs (G : J → J → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, G a b = ∑ p ∈ pairs J, (G p.1 p.2 + G p.2 p.1) := by sorry
