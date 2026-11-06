-- Prove2me | Theorems.Thm_ExplicitCost_totalsAre
-- name    : ExplicitCost.totalsAre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:08.079047+00:00
-- url     : https://prove2.me/theorems/5d27dea7-6658-4969-8d6b-c77323b68a36
-- title:
--   Explicit Cost: totals Are
-- statement:
--   **The totals that the solver compares are the totals U of the two networks.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Totals.lean#L48-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Totals.lean#L48-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_GeneralPieces_Rec_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Totals
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data}

theorem ExplicitCost.totalsAre : TotalsAre := by sorry
