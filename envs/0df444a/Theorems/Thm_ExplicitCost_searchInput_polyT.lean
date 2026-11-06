-- Prove2me | Theorems.Thm_ExplicitCost_searchInput_polyT
-- name    : ExplicitCost.searchInput_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:48.901193+00:00
-- url     : https://prove2.me/theorems/992c67a1-b0b3-4b0d-ad8f-a2c3bfb44d08
-- title:
--   Explicit Cost: search Input poly T
-- statement:
--   What the search is given.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L69-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolySolverData.lean#L69-L69

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

theorem ExplicitCost.searchInput_polyT (c : ℕ) {v : α → Ready × ℕ} (hv : PolyT v) : PolyT fun t => searchInput c (v t) := by sorry
