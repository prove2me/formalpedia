-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_gval_ite
-- name    : CircuitLowerBound.Clause.gval_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:49:18.617223+00:00
-- url     : https://prove2.me/theorems/42097580-203f-484c-820f-7118b0488360
-- title:
--   Clause: gval ite
-- statement:
--   The Clause construction uses the gval ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L172-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L172-L174

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.gval_ite (v : ℕ → Bool) (c : Bool) (o₁ o₂ : B4) (i j : ℕ) :
    gval v ((if c then o₁ else o₂), i, j) = if c then gval v (o₁, i, j) else gval v (o₂, i, j) := by sorry
