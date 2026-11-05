-- Prove2me | Theorems.Thm_ClauseBound_TopN_Arith_root17_spec
-- name    : ClauseBound.TopN.Arith.root17_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:56:38.135097+00:00
-- url     : https://prove2.me/theorems/86081085-1e89-41f5-857f-7e2a98d81846
-- title:
--   Arith: root17 spec
-- statement:
--   The length of `root17 m` is the integer part of the seventeenth root of m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L34-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Arith.lean#L34-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_Arith
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith

theorem ClauseBound.TopN.Arith.root17_spec (m : ℕ) : (root17 m).length ^ 17 ≤ m ∧ m < ((root17 m).length + 1) ^ 17 := by sorry
