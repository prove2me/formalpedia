-- Prove2me | Theorems.Thm_CircuitLowerBound_Norm_length_norm
-- name    : CircuitLowerBound.Norm.length_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:43:41.143589+00:00
-- url     : https://prove2.me/theorems/65bb2928-6cf6-47b2-b372-10285cbb983e
-- title:
--   Norm: length norm
-- statement:
--   The Norm construction uses the length norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Norm.lean#L42-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Norm
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Norm

theorem CircuitLowerBound.Norm.length_norm (C : Circuit) (n : ℕ) : (norm n C).length = C.length := by sorry
