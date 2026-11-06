-- Prove2me | Theorems.Thm_ExplicitCost_crude_second
-- name    : ExplicitCost.crude_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:20:32.210536+00:00
-- url     : https://prove2.me/theorems/627ddd15-676a-4b53-a425-3bd4c0b68f1c
-- title:
--   Explicit Cost: crude second
-- statement:
--   g(P + B₁) in plain variables: s is λ + B, T is (2λ)^c, E is Ξ^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L44-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CrudeBounds.lean#L44-L58

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

theorem ExplicitCost.crude_second (g lam B s T E : ℕ) (hg : 3 ≤ g) (hl : lam ≤ s) (hB : B ≤ s) (hs : 2 ≤ s) (hT : T ≤ E) (hE : 1 ≤ E) :
    g * (g ^ 3 * lam + (g * B + g ^ 2 * T)) ≤ E * (g ^ 2 * s) ^ 4 := by sorry
