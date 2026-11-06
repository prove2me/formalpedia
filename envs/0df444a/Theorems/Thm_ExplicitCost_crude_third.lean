-- Prove2me | Theorems.Thm_ExplicitCost_crude_third
-- name    : ExplicitCost.crude_third
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:17:38.87841+00:00
-- url     : https://prove2.me/theorems/afffd40b-51e1-44df-8152-7a37fe0eedcb
-- title:
--   Explicit Cost: crude third
-- statement:
--   g(2N + 1 + g²B₁) in plain variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L61-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L61-L77

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

theorem ExplicitCost.crude_third (g lam B s T E : ℕ) (hg : 3 ≤ g) (hl : lam ≤ s) (hB : B ≤ s) (hs : 2 ≤ s) (hT : T ≤ E) (hE : 1 ≤ E) :
    g * (g ^ 4 * lam + 1 + (g ^ 4 * lam + g ^ 2 * (g * B + g ^ 2 * T))) ≤ E * (g ^ 2 * s) ^ 5 := by sorry
