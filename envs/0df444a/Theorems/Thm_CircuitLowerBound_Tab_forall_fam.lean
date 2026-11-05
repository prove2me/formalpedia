-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_forall_fam
-- name    : CircuitLowerBound.Tab.forall_fam
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:31:45.030727+00:00
-- url     : https://prove2.me/theorems/1d8e1779-b2e9-4694-b14a-5bee295b4bb4
-- title:
--   Tab: forall fam
-- statement:
--   The Tab construction uses the forall fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L65-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}

theorem CircuitLowerBound.Tab.forall_fam {ι : Type} [Finite ι] {f : ι → YCl N} {p : YCl N → Prop} : (∀ c ∈ fam f, p c) ↔ ∀ i, p (f i) := by sorry
