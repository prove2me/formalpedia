-- Prove2me | Theorems.Thm_CountKSatRate_Top_le_roundS
-- name    : CountKSatRate.Top.le_roundS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:43:30.591995+00:00
-- url     : https://prove2.me/theorems/13b34c38-a48e-4524-bd77-e334d8538fc7
-- title:
--   Top: le round S
-- statement:
--   One round does not lower the number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Top.lean#L29-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Top.lean#L29-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Top
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Top
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)

theorem CountKSatRate.Top.le_roundS {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (st : List σ × ℕ) : st.2 ≤ (roundS step val st).2 := by sorry
