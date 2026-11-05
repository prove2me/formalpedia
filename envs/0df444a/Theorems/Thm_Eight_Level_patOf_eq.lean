-- Prove2me | Theorems.Thm_Eight_Level_patOf_eq
-- name    : Eight.Level.patOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:07:34.925821+00:00
-- url     : https://prove2.me/theorems/de5f142d-7505-4627-9557-59f2ec098c4a
-- title:
--   Level: pat Of eq
-- statement:
--   The Level construction uses the pat Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L42-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecLevel_GridWords.lean#L42-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Paper_mem_rectangles

set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}

theorem Eight.Level.patOf_eq (g lam y : ℕ) {q : Rectangle g} (hq : q ∈ rectangles g) : Eight.Level.patOf g lam y q = digOf g lam y q := by sorry
