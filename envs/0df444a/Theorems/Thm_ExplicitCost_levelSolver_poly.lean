-- Prove2me | Theorems.Thm_ExplicitCost_levelSolver_poly
-- name    : ExplicitCost.levelSolver_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:18:47.386608+00:00
-- url     : https://prove2.me/theorems/3652cde4-eedd-45c2-afcc-a4863127eaa3
-- title:
--   Explicit Cost: level Solver poly
-- statement:
--   The solver at a level ℓ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolver.lean#L44-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolver.lean#L44-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolySolverData
import Definitions.Def_CountedRecursion_PolyRules
import Definitions.Def_CountedRecursion_Numbers
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolySolver
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.levelSolver_poly (hG : groupingCall.PolyTimeSteps) (c x₀ : ℕ) : (levelSolver c x₀).PolyTimeSteps := by sorry
