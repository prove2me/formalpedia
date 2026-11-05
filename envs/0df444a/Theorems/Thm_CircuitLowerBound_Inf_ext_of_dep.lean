-- Prove2me | Theorems.Thm_CircuitLowerBound_Inf_ext_of_dep
-- name    : CircuitLowerBound.Inf.ext_of_dep
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:10:33.453207+00:00
-- url     : https://prove2.me/theorems/951facce-14ea-4a3e-ae3a-c20bcae5e43e
-- title:
--   Inf: ext of dep
-- statement:
--   Every function that depends on the first k input bits only can be made available.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L89-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L89-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP

theorem CircuitLowerBound.Inf.ext_of_dep {n : ℕ} : ∀ k, k ≤ n → ∀ g : List Bool → Bool,
    (∀ x y : List Bool, x.length = n → y.length = n → x.take k = y.take k → g x = g y) → Ext n g := by sorry
