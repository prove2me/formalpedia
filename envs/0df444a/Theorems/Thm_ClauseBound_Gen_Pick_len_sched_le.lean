-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_len_sched_le
-- name    : ClauseBound.Gen.Pick.len_sched_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:06.723379+00:00
-- url     : https://prove2.me/theorems/2dfabe24-0d9a-4674-ac40-9c35561e663d
-- title:
--   Pick: len sched le
-- statement:
--   The Pick construction uses the len sched le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L99-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L99-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_Pick
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Pick
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

theorem ClauseBound.Gen.Pick.len_sched_le (P : PiecesF) (x₀ k : ℕ) : ∀ l, K x₀ l ≤ k → len (sched P x₀ l) ≤ l * stepB P.m k + 2
  := by sorry
