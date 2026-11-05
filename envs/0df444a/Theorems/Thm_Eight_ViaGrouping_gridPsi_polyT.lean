-- Prove2me | Theorems.Thm_Eight_ViaGrouping_gridPsi_polyT
-- name    : Eight.ViaGrouping.gridPsi_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:20.142852+00:00
-- url     : https://prove2.me/theorems/366889c3-bb95-4bd3-9067-31e5c3d03743
-- title:
--   Via Grouping: grid Psi poly T
-- statement:
--   **The program for Ψ is polynomial-time**, as a function of λ, y and the query, for fixed g and a
--   fixed direction.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L177-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L177-L180

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
variable {α : Type} [Enc α]

theorem Eight.ViaGrouping.gridPsi_polyT (g : ℕ) (tr : Bool) {lam y : α → ℕ} {q : α → PsiQ} (hl : PolyT lam) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => gridPsi g tr (lam x) (y x) (q x) := by sorry
