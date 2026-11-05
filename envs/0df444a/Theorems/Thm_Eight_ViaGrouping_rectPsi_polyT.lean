-- Prove2me | Theorems.Thm_Eight_ViaGrouping_rectPsi_polyT
-- name    : Eight.ViaGrouping.rectPsi_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:04.363125+00:00
-- url     : https://prove2.me/theorems/df018c24-ad22-4306-83bd-e9a0b20ddfb7
-- title:
--   Via Grouping: rect Psi poly T
-- statement:
--   The factor of one rectangle is polynomial-time: four strings are cut out of the two settings, a
--   digit of y is computed, and A_i is «computable in time poly(λ)» (Lemma 2(a)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L140-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L140-L153

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

theorem Eight.ViaGrouping.rectPsi_polyT (g : ℕ) (tr : Bool) {lam y a b i i' : α → ℕ} {z z' : α → List Bool} (hl : PolyT lam) (hy : PolyT y) (ha : PolyT a) (hb : PolyT b)
    (hz : PolyT z) (hz' : PolyT z') (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => rectPsi g tr (lam x) (y x) (a x) (b x) (z x) (z' x) (i x) (i' x) := by sorry
