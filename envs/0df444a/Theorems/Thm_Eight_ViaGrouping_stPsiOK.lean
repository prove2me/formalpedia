-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stPsiOK
-- name    : Eight.ViaGrouping.stPsiOK
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:48.507602+00:00
-- url     : https://prove2.me/theorems/c3afccdc-b855-45a6-873e-39f3be59835b
-- title:
--   Via Grouping: st Psi OK
-- statement:
--   The program `gridPsi` computes Ψ: for λ ≥ 1, every ι (a number y < (t + 1)^{|ℛ|}), two different
--   rows (columns) a, b and settings z, z' of them, gridPsi g tr λ y ((a, b), (z, z')) is Ψ_{a,b}(z, z')
--   of the network `Eight.Level.netOfι` that Algorithm 1 runs. This is what the
--   algorithm of one level asks of the function for Ψ (`StPsiOK`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L130-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/GridPsi.lean#L130-L130

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

theorem Eight.ViaGrouping.stPsiOK (g : ℕ) (tr : Bool) : StPsiOK g tr (gridPsi g tr) := by sorry
