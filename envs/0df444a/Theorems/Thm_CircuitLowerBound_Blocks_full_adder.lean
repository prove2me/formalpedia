-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_full_adder
-- name    : CircuitLowerBound.Blocks.full_adder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:41:32.72277+00:00
-- url     : https://prove2.me/theorems/ee3b864c-6b69-473c-bf53-3d9d44e90eee
-- title:
--   Blocks: full adder
-- statement:
--   A chain of full adders: s i = a i ⊕ d i ⊕ c i, c (i+1) = (a i ∧ d i) ∨ ((a i ⊕ d i) ∧ c i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L306-L318
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L306-L318

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Blocks
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Blocks
open ENP Groundwork

theorem CircuitLowerBound.Blocks.full_adder (a d s c : ℕ → Bool) (w : ℕ) (hs : ∀ i < w, s i = ((a i ^^ d i) ^^ c i))
    (hc : ∀ i < w, c (i + 1) = ((a i && d i) || ((a i ^^ d i) && c i))) :
    ∀ m ≤ w, num s m + 2 ^ m * (c m).toNat = num a m + num d m + (c 0).toNat := by sorry
