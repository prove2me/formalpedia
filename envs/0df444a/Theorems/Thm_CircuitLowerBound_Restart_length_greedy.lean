-- Prove2me | Theorems.Thm_CircuitLowerBound_Restart_length_greedy
-- name    : CircuitLowerBound.Restart.length_greedy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:23.529219+00:00
-- url     : https://prove2.me/theorems/f3e2f22d-8ff2-47fd-8111-15d9fa10b507
-- title:
--   Restart: length greedy
-- statement:
--   The search has set j variables after j steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L37-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L37-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Theorems.Thm_CircuitLowerBound_SmallFacts_length_greedy
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open CircuitLowerBound.Restart

theorem CircuitLowerBound.Restart.length_greedy (φ : Cnf) (j : ℕ) : (greedy φ j).length = j := by sorry
