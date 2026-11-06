-- Prove2me | Theorems.Thm_ExplicitCost_parentAt_polyT
-- name    : ExplicitCost.parentAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:13:42.282396+00:00
-- url     : https://prove2.me/theorems/ee6a00d2-936f-42d0-800d-05f646792ce7
-- title:
--   Explicit Cost: parent At poly T
-- statement:
--   The parent that is handed to the callee.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L66-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L66-L66

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

theorem ExplicitCost.parentAt_polyT {v : α → Ready × ℕ} {x : α → ℕ} (hv : PolyT v) (hx : PolyT x) : PolyT fun t => parentAt (v t) (x t) := by sorry
