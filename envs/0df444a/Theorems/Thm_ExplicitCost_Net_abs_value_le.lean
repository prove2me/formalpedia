-- Prove2me | Theorems.Thm_ExplicitCost_Net_abs_value_le
-- name    : ExplicitCost.Net.abs_value_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:08.064204+00:00
-- url     : https://prove2.me/theorems/32686eca-9923-4d43-b636-22c3ba8920ec
-- title:
--   Net: abs value le
-- statement:
--   A network on [g] with parameters P, B has |Z| ≤ 2^{gP + g²B}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L90-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L90-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
import Theorems.Thm_ClauseBound_Alg_Level_abs_value_le
import Theorems.Thm_Groundwork_Prog_abs_value_le

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.Net.abs_value_le {g : ℕ} (N : Net g) {P B : ℕ} (h : N.Is P B) : |N.value| ≤ 2 ^ (g * P + g * g * B) := by sorry
