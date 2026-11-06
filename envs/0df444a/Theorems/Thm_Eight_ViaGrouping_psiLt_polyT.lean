-- Prove2me | Theorems.Thm_Eight_ViaGrouping_psiLt_polyT
-- name    : Eight.ViaGrouping.psiLt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:51.789567+00:00
-- url     : https://prove2.me/theorems/9ea93871-1fab-40f4-a111-47a24560bd04
-- title:
--   Via Grouping: psi Lt poly T
-- statement:
--   Ψ_{a,b} for a < b is polynomial-time: a test on g pairs of strings and a product of g² factors.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L156-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L156-L173

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

theorem Eight.ViaGrouping.psiLt_polyT (g : ℕ) (tr : Bool) {lam y a b : α → ℕ} {z z' : α → List Bool} (hl : PolyT lam) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b)
    (hz : PolyT z) (hz' : PolyT z') : PolyT fun x => psiLt g tr (lam x) (y x) (a x) (b x) (z x) (z' x) := by sorry
