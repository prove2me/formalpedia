-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_pref_ofFn
-- name    : CircuitLowerBound.Tab.pref_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:28:40.892385+00:00
-- url     : https://prove2.me/theorems/df4f24e7-c6d6-455a-9e40-3bc5d2ff1eb1
-- title:
--   Tab: pref of Fn
-- statement:
--   The first d cells of a stack give back its top d symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L131-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L131-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing

theorem CircuitLowerBound.Tab.pref_ofFn {α : Type} (d : ℕ) : ∀ S : List α, pref (List.ofFn fun j : Fin d => S[j.val]?) = S.take d := by sorry
