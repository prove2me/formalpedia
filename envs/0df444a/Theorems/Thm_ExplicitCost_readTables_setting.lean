-- Prove2me | Theorems.Thm_ExplicitCost_readTables_setting
-- name    : ExplicitCost.readTables_setting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:30.732515+00:00
-- url     : https://prove2.me/theorems/2db79474-4530-4891-974c-95c2f76e2894
-- title:
--   Explicit Cost: read Tables setting
-- statement:
--   Tables made an oracle and read back are the tables, on settings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L37-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.readTables_setting {K lam : ℕ} (W : ℕ → List Bool → ℤ) {w : ℕ} {z : List Bool} (hw : w < K) (hz : z.length = (K - 1) * lam) : readTables (answersOf K lam W) w z = W w z := by sorry
