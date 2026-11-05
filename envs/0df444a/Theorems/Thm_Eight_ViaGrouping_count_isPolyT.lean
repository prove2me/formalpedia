-- Prove2me | Theorems.Thm_Eight_ViaGrouping_count_isPolyT
-- name    : Eight.ViaGrouping.count_isPolyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:19:10.570307+00:00
-- url     : https://prove2.me/theorems/c2c514fc-40f8-44ad-a33f-524ae76ff59d
-- title:
--   Via Grouping: count is Poly T
-- statement:
--   The machine has polynomial-time steps if the algorithm has them whenever the procedures have and
--   P is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L50-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper

theorem Eight.ViaGrouping.count_isPolyT {NA : NetAlg} (h : AlgKeeps NA) (g k : ℕ) : Nonempty (IsPolyT (NA.app (satProcs g k))) := by sorry
