-- Prove2me | Theorems.Thm_ExplicitCost_rK_readyOf
-- name    : ExplicitCost.rK_readyOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:16.197705+00:00
-- url     : https://prove2.me/theorems/84e5fd82-a744-428e-8c81-465c7abb89a9
-- title:
--   Explicit Cost: r K ready Of
-- statement:
--   The K that the solver holds at the level ℓ + 1 is K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L43-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L43-L46

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

theorem ExplicitCost.rK_readyOf (hl : hLev h = l + 1) : rK (readyOf D x₀ h) = Levels.Gen.K x₀ l := by sorry
