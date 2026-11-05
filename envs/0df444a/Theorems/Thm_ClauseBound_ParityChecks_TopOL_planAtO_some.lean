-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_TopOL_planAtO_some
-- name    : ClauseBound.ParityChecks.TopOL.planAtO_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:56.238255+00:00
-- url     : https://prove2.me/theorems/d9ec93da-334a-418b-9651-cbfda176281a
-- title:
--   Top OL: plan At O some
-- statement:
--   What a plan says.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L31-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L31-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem ClauseBound.ParityChecks.TopOL.planAtO_some {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) {c n₀ k n s v : ℕ} {i : Idx} (h : planAtO S c n₀ k n i s = some v) :
    (s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n) ∧ v = needO S k i n s := by sorry
