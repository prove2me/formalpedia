-- Prove2me | Theorems.Thm_Eight_ViaGrouping_psiLt_eq
-- name    : Eight.ViaGrouping.psiLt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:33:00.455045+00:00
-- url     : https://prove2.me/theorems/601de324-10b6-4635-862c-ebfec384c76d
-- title:
--   Via Grouping: psi Lt eq
-- statement:
--   The loop and the test of `psiLt` written as products: over the g straight edges, and over the
--   pairs i < i'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L40-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L40-L53

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
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.psiLt_eq (g : ℕ) (tr : Bool) (lam y a b : ℕ) (z z' : List Bool) :
    psiLt g tr lam y a b z z' =
      (∏ i : Fin g, if heG g g lam z i (nodeG g tr b i) = heG g g lam z' i (nodeG g tr a i) then 1 else 0) *
      ∏ k : Fin g × Fin g with k.1 < k.2, rectPsi g tr lam y a b z z' k.1 k.2 := by sorry
