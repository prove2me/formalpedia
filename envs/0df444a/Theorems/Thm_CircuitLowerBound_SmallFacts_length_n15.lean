-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_length_n15
-- name    : CircuitLowerBound.SmallFacts.length_n15
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:55:00.909587+00:00
-- url     : https://prove2.me/theorems/c9d93e31-53f9-44ac-8f8f-b911409a2f84
-- title:
--   Small Facts: length n15
-- statement:
--   The Small Facts construction uses the length n15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L147-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L147-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts

theorem CircuitLowerBound.SmallFacts.length_n15 (c : TCl) : (n15 c).length = 15 := by sorry
