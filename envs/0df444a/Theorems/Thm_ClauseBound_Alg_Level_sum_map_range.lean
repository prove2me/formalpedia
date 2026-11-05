-- Prove2me | Theorems.Thm_ClauseBound_Alg_Level_sum_map_range
-- name    : ClauseBound.Alg.Level.sum_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:01.887522+00:00
-- url     : https://prove2.me/theorems/f31c8117-f68f-4c42-bfaa-07c6e2c4eb13
-- title:
--   Level: sum map range
-- statement:
--   A sum over a list of numbers 0, …, n − 1 is a sum over a range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Level.lean#L32-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Level.lean#L32-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Level
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Stepped_sum_map_range
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset

theorem ClauseBound.Alg.Level.sum_map_range (f : ℕ → ℤ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by sorry
