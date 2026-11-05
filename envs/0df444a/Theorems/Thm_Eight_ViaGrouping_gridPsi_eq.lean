-- Prove2me | Theorems.Thm_Eight_ViaGrouping_gridPsi_eq
-- name    : Eight.ViaGrouping.gridPsi_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:57.889935+00:00
-- url     : https://prove2.me/theorems/3084d0c7-1f05-4788-80fd-c7ce450f32e7
-- title:
--   Via Grouping: grid Psi eq
-- statement:
--   **The program computes Ψ_{a,a'}** of the row network and of the column network that Algorithm 1
--   runs, at all words of g·g²·λ bits. «Ψ_{a,a'} is the product of the factors of the g straight edges
--   between rows a and a' and of A_{ι(q)}(x_q, y_q, u_q, v_q) over the
--   g(g−1)/2 rectangles q with these two rows.» Same as in the paper; it holds for every number y,
--   because a digit in base t + 1 is at most t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L115-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L115-L121

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_GridPsiDefs
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_SecCrossing_Cert
import Definitions.Def_Eight_Level_Presents
import Definitions.Def_Eight_Level_Cert
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.gridPsi_eq {g lam : ℕ} (hlam : 1 ≤ lam) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hz' : z'.length = nMemb g g tr * (g * g) * lam) :
    gridPsi g tr lam y ((a.val, b.val), (z, z')) = (netOfι g tr lam y Rm).Ψ a b z z' := by sorry
