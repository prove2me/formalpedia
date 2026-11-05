-- Prove2me | Theorems.Thm_CircuitLowerBound_Inf_wires_concat
-- name    : CircuitLowerBound.Inf.wires_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:09:07.903+00:00
-- url     : https://prove2.me/theorems/e3bc9238-3a0d-4cd2-aa35-da9850f48d7e
-- title:
--   Inf: wires concat
-- statement:
--   The Inf construction uses the wires concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP

theorem CircuitLowerBound.Inf.wires_concat (x : List Bool) (C : Circuit) (G : Gate) :
    wires x (C ++ [G]) = wires x C ++ [G.op ((wires x C).getD G.in₁ false) ((wires x C).getD G.in₂ false)] := by sorry
