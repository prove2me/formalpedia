-- Prove2me | Theorems.Thm_ExplicitCost_rG_readyOf
-- name    : ExplicitCost.rG_readyOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:19:26.678307+00:00
-- url     : https://prove2.me/theorems/20fc4265-44e0-4571-a2ab-b93ce3a1b412
-- title:
--   Explicit Cost: r G ready Of
-- statement:
--   The g that the solver holds at the level ℓ + 1 is g_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L49-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L49-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ}

theorem ExplicitCost.rG_readyOf (hl : hLev h = l + 1) : rG (readyOf D x₀ h) = Levels.Gen.g x₀ l := by sorry
