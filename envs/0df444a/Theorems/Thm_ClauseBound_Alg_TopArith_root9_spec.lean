-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_root9_spec
-- name    : ClauseBound.Alg.TopArith.root9_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:22.990969+00:00
-- url     : https://prove2.me/theorems/7f998c83-f829-4b8d-879c-02b90924ea95
-- title:
--   Top Arith: root9 spec
-- statement:
--   root9 m is the integer part of the ninth root of m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L62-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L62-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F

theorem ClauseBound.Alg.TopArith.root9_spec (m : ℕ) : (root9 m).length ^ 9 ≤ m ∧ m < ((root9 m).length + 1) ^ 9 := by sorry
