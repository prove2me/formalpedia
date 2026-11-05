-- Prove2me | Theorems.Thm_CircuitLowerBound_Acc_mono
-- name    : CircuitLowerBound.Acc.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:31:38.359701+00:00
-- url     : https://prove2.me/theorems/58e72b17-52fb-426c-81fa-cfe27d35e338
-- title:
--   Acc: mono
-- statement:
--   The Acc construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Main.lean#L27-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Main.lean#L27-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing

theorem CircuitLowerBound.Acc.mono {N : TM2ComputableAux Bool Bool} {P T T' : ℕ} (h : Acc N P T) (hT : T ≤ T') : Acc N P T' := by sorry
