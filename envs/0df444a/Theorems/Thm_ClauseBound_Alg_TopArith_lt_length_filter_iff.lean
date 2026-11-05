-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopArith_lt_length_filter_iff
-- name    : ClauseBound.Alg.TopArith.lt_length_filter_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:19:55.583269+00:00
-- url     : https://prove2.me/theorems/03dbc47e-5e55-49aa-839b-2e29897f6651
-- title:
--   Top Arith: lt length filter iff
-- statement:
--   For a property that passes to smaller numbers, the number of b < n that have it is the first
--   number below n that does not have it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L35-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopArith.lean#L35-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_ClauseBound_Alg_TopArith
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopArith
open PaddedDescent.F

theorem ClauseBound.Alg.TopArith.lt_length_filter_iff (p : ℕ → Bool) (hp : ∀ a b, a ≤ b → p b = true → p a = true) (n : ℕ) :
    ∀ b < n, (p b = true ↔ b < ((List.range n).filter p).length) := by sorry
