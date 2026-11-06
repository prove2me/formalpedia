-- Prove2me | Theorems.Thm_ExplicitCost_crude_plain
-- name    : ExplicitCost.crude_plain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:17:15.89401+00:00
-- url     : https://prove2.me/theorems/4e91f134-7607-48bc-a844-55c559a142a0
-- title:
--   Explicit Cost: crude plain
-- statement:
--   The crude bounds for all numbers 3 ≤ K ≤ g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L80-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L80-L96

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

theorem ExplicitCost.crude_plain (c K g lam B L : ℕ) (hK : 3 ≤ K) (hKg : K ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hL : L ≤ g ^ 4 * lam + 1) :
    bitsOut K g (g ^ 3 * lam) (bitsOne c g lam B) ≤ g ^ 4 * lam + g ^ 2 * bitsOne c g lam B ∧
    g * (g ^ 3 * lam + bitsOne c g lam B) ≤ Xi g lam B ^ (c + 4) ∧
    K * (L + bitsOut K g (g ^ 3 * lam) (bitsOne c g lam B)) ≤ Xi g lam B ^ (c + 5) := by sorry
