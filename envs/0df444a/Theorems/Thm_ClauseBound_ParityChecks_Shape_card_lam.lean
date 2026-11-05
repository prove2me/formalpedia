-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Shape_card_lam
-- name    : ClauseBound.ParityChecks.Shape.card_lam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:49:27.571796+00:00
-- url     : https://prove2.me/theorems/54e7e9b8-0830-4b6c-b86e-1166741cb236
-- title:
--   Shape: card lam
-- statement:
--   A check as a set has as many members as the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L145-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Shape.lean#L145-L151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Shape
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Shape
open Finset Groundwork.Prog PaddedDescent.F.Mark _root_.ParityChecks ClauseBound.ParityChecks

theorem ClauseBound.ParityChecks.Shape.card_lam {m : ℕ} (Lam : List Chk) (j' : ℕ) (hL : (Lam.getD j' []).Nodup) (hm : ∀ x ∈ Lam.getD j' [], x < m) :
    #(lam m Lam j') = (Lam.getD j' []).length := by sorry
