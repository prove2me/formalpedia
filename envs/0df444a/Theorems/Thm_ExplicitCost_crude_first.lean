-- Prove2me | Theorems.Thm_ExplicitCost_crude_first
-- name    : ExplicitCost.crude_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:16:49.190453+00:00
-- url     : https://prove2.me/theorems/1b0b2b32-5f7f-46c0-8ede-7a413a23a2e5
-- title:
--   Explicit Cost: crude first
-- statement:
--   B' ≤ N + g²B₁: ⌈2N/K⌉ ≤ N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L29-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L29-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CrudeBounds
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.crude_first (K g lam B₁ : ℕ) (hK : 3 ≤ K) (hg : 3 ≤ g) (hlam : 1 ≤ lam) : bitsOut K g (g ^ 3 * lam) B₁ ≤ g ^ 4 * lam + g ^ 2 * B₁ := by sorry
