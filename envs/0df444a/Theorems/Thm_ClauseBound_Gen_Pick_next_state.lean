-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_next_state
-- name    : ClauseBound.Gen.Pick.next_state
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:47:43.504598+00:00
-- url     : https://prove2.me/theorems/61a542ee-7454-4509-85fe-2a289d6f2e49
-- title:
--   Pick: next state
-- statement:
--   The Pick construction uses the next state property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L77-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L77-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Pick.next_state (P : PiecesF) (x₀ l : ℕ) (b : U) :
    next b (state P x₀ l) = if K x₀ (l + 1) ≤ b.length then state P x₀ (l + 1) else state P x₀ l := by sorry
