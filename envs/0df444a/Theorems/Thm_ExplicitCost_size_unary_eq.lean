-- Prove2me | Theorems.Thm_ExplicitCost_size_unary_eq
-- name    : ExplicitCost.size_unary_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:10.58606+00:00
-- url     : https://prove2.me/theorems/173e43fa-0173-4598-b6aa-49410f0fe9fb
-- title:
--   Explicit Cost: size unary eq
-- statement:
--   The size of n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L36-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentSize.lean#L36-L39

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

theorem ExplicitCost.size_unary_eq (n : ℕ) : size (unary n) = 2 * n + 1 := by sorry
