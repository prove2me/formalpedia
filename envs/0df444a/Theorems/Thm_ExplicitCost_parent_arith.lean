-- Prove2me | Theorems.Thm_ExplicitCost_parent_arith
-- name    : ExplicitCost.parent_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:31.90211+00:00
-- url     : https://prove2.me/theorems/79f2dee3-da52-4478-a82f-1a3c1b00868f
-- title:
--   Explicit Cost: parent arith
-- statement:
--   The arithmetic: with X = g²(λ + B) ≥ 8 and m = (2λ)^c ≤ X^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L69-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L69-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentSize
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.parent_arith {X m c K g lam B R sy sx sl : ℕ} (hX : 8 ≤ X) (hm : m ≤ X ^ c) (hK : K ≤ X) (hg : g ≤ X) (hlam : 2 * lam ≤ X) (hB : B ≤ X) (hR : R ≤ X * X) (hsy : sy ≤ m * R + 1) (hsx : sx ≤ X + 1)
    (hsl : sl ≤ (m * (m + 1 + 1) + 1) + ((m * (2 * lam + 1 + 1) + 1) + (m * (2 * lam + 1 + 1) + 1))) :
    (2 * K + 1 + (2 * g + 1)) + ((2 * lam + 1 + (2 * B + 1)) + (sl + (1 + (sy + sx)))) ≤ X ^ (2 * c + 4) := by sorry
