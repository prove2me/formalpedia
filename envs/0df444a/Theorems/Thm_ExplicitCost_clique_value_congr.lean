-- Prove2me | Theorems.Thm_ExplicitCost_clique_value_congr
-- name    : ExplicitCost.clique_value_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:52.76048+00:00
-- url     : https://prove2.me/theorems/5467905f-fef6-487f-b806-307ba34fd0c2
-- title:
--   Explicit Cost: clique value congr
-- statement:
--   The value of a clique reads its tables only on settings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L30-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L30-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.clique_value_congr {K lam : ℕ} {W W' : Fin K → List Bool → ℤ} (h : ∀ w, ∀ z ∈ words ((K - 1) * lam), W w z = W' w z) : (clique K lam W).value = (clique K lam W').value := by sorry
