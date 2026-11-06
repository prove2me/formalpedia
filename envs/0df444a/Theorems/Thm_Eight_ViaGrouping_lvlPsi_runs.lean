-- Prove2me | Theorems.Thm_Eight_ViaGrouping_lvlPsi_runs
-- name    : Eight.ViaGrouping.lvlPsi_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:35.173516+00:00
-- url     : https://prove2.me/theorems/d98c1ab0-9107-4f1d-9872-19d7af97646c
-- title:
--   Via Grouping: lvl Psi runs
-- statement:
--   A plain function run as a procedure for Ψ: one step; the states are the query and the answer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L74-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L74-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.lvlPsi_runs {C : Type} [HasSize C] (psi : ℕ → ℕ → PsiQ → ℤ) (lam : C → ℕ) (c : C) {y g a b L Bv : ℕ} {z z' : List Bool} {v : ℤ}
    (hv : psi (lam c) y ((a, b), (z, z')) = v) (ha : a < g) (hb : b < g) (hz : z.length = L) (hz' : z'.length = L) (hB : |v| ≤ 2 ^ Bv) :
    (ofFun fun x : (C × ℕ) × PsiQ => psi (lam x.1.1) x.1.2 x.2).Runs ((c, y), ((a, b), (z, z'))) 1 (size c + size y + 2 * size g + 4 * L + Bv + 8) v := by sorry
