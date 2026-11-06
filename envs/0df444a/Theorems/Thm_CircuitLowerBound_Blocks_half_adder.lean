-- Prove2me | Theorems.Thm_CircuitLowerBound_Blocks_half_adder
-- name    : CircuitLowerBound.Blocks.half_adder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:14.977901+00:00
-- url     : https://prove2.me/theorems/71d995e3-0e95-4aae-8d60-0c26d1ed8fa0
-- title:
--   Blocks: half adder
-- statement:
--   A chain of half adders: s i = a i ⊕ c i, c (i+1) = a i ∧ c i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L292-L303
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Blocks.lean#L292-L303

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

theorem CircuitLowerBound.Blocks.half_adder (a s c : ℕ → Bool) (w : ℕ) (hs : ∀ i < w, s i = (a i ^^ c i)) (hc : ∀ i < w, c (i + 1) = (a i && c i)) :
    ∀ m ≤ w, num s m + 2 ^ m * (c m).toNat = num a m + (c 0).toNat := by sorry
