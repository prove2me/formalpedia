-- Prove2me | Theorems.Thm_Eight_ViaGrouping_psiLt_row
-- name    : Eight.ViaGrouping.psiLt_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:54.813871+00:00
-- url     : https://prove2.me/theorems/2c97d816-2368-4474-a480-4ee9431f22c4
-- title:
--   Via Grouping: psi Lt row
-- statement:
--   Ψ_{a,a'} of the row network that Algorithm 1 runs, for a < a'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L65-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L65-L81

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

theorem Eight.ViaGrouping.psiLt_row {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    psiLt g false lam y a b z z' = (netOfι g false lam y Rm).Ψ a b z z' := by sorry
