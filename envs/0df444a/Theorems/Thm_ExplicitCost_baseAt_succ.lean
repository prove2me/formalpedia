-- Prove2me | Theorems.Thm_ExplicitCost_baseAt_succ
-- name    : ExplicitCost.baseAt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:17:55.319499+00:00
-- url     : https://prove2.me/theorems/c3d88aba-6a74-4708-993a-80cc1d17d249
-- title:
--   Explicit Cost: base At succ
-- statement:
--   X_{j+1} is the Ξ of the callers of the depth j + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Chain.lean#L27-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Chain.lean#L27-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ChainLabel
import Definitions.Def_CountedRecursion_CrudeBounds
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_CountedRecursion_PartAPrinted
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Chain
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed

theorem ExplicitCost.baseAt_succ (ρ : ℝ) (c x₀ l lam B j : ℕ) : baseAt ρ c x₀ l lam B (j + 1) = xiAt ρ c x₀ l lam B j := by sorry
