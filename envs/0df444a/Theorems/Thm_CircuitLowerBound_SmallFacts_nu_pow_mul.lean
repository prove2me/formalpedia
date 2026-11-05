-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_nu_pow_mul
-- name    : CircuitLowerBound.SmallFacts.nu_pow_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:42:13.035999+00:00
-- url     : https://prove2.me/theorems/516b9fd0-473f-4ecd-ad34-37e743f626a4
-- title:
--   Small Facts: nu pow mul
-- statement:
--   The Small Facts construction uses the nu pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L33-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L33-L37

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

theorem CircuitLowerBound.SmallFacts.nu_pow_mul (a s : ℕ) : nu (2 ^ a * (2 * s + 1)) = a := by sorry
