-- Prove2me | Theorems.Thm_Eight_ViaGrouping_levelProcs_keepsP
-- name    : Eight.ViaGrouping.levelProcs_keepsP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:13.856209+00:00
-- url     : https://prove2.me/theorems/1269c295-355e-450d-a988-390621629abe
-- title:
--   Via Grouping: level Procs keeps P
-- statement:
--   The row network and the column network of ι, given as Definition 2(iii) asks, have P = g³λ, P_a
--   and c_{a,b} in unary and four procedures with polynomial-time steps, for λ in unary. The test for
--   membership says yes without looking at the query.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelCert.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelCert.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_Level_Cert
import Definitions.Def_Eight_ViaGrouping_LevelCert
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg Stepped Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.levelProcs_keepsP (h : Eight.StKeeps) (g : ℕ) (tr : Bool) {psi : ℕ → ℕ → PsiQ → ℤ} (hp : StPsiPoly psi) (C : Type) [HasSize C] [Enc C] [Carried C] (lam : C → ℕ)
    (R : Stepped (C × IQ) ℤ) (hl : Unary lam) (hR : Nonempty (IsPolyT R)) : KeepsP (levelProcs g tr psi lam R) := by sorry
