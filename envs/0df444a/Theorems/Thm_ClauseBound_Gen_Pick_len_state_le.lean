-- Prove2me | Theorems.Thm_ClauseBound_Gen_Pick_len_state_le
-- name    : ClauseBound.Gen.Pick.len_state_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:47:48.879444+00:00
-- url     : https://prove2.me/theorems/906bbe52-978b-4656-8e2b-2754b4564da6
-- title:
--   Pick: len state le
-- statement:
--   The Pick construction uses the len state le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L114-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/Pick.lean#L114-L124

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

theorem ClauseBound.Gen.Pick.len_state_le (P : PiecesF) (x₀ k r l : ℕ) (hk : K x₀ l ≤ k) (hl : l ≤ r) : len (state P x₀ l) ≤ lenB P.m r k := by sorry
