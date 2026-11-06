-- Prove2me | Theorems.Thm_ExplicitCost_child_polyT
-- name    : ExplicitCost.child_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:47.154703+00:00
-- url     : https://prove2.me/theorems/01e7c934-856c-4c43-bf60-2190383a8ba7
-- title:
--   Explicit Cost: child poly T
-- statement:
--   The context of the call.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L72-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L72-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_PolyQueries
import Definitions.Def_ClauseBound_Alg_CertLevel
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolySolverData
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
variable {α : Type} [Enc α]

theorem ExplicitCost.child_polyT {z : α → (Ready × ℕ) × CliqueCall} (hz : PolyT z) : PolyT fun t => child (z t) := by sorry
