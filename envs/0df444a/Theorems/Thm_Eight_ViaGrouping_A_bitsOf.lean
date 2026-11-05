-- Prove2me | Theorems.Thm_Eight_ViaGrouping_A_bitsOf
-- name    : Eight.ViaGrouping.A_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:33:14.376407+00:00
-- url     : https://prove2.me/theorems/cde85f7f-ddba-4cb9-af24-a3408eb11815
-- title:
--   Via Grouping: A bits Of
-- statement:
--   The program of the proof of Lemma 2(a) computes A_i at four words of λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L56-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L56-L60

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

theorem Eight.ViaGrouping.A_bitsOf {lam : ℕ} (i : ℕ) {X Y U V : List Bool} (hX : X.length = lam) (hY : Y.length = lam) (hU : U.length = lam) (hV : V.length = lam) :
    A lam i (Grid.bitsOf lam X) (Grid.bitsOf lam Y) (Grid.bitsOf lam U) (Grid.bitsOf lam V) = aMul (i, X, Y, U, V) := by sorry
