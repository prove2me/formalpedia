-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_bits_foldr
-- name    : CircuitLowerBound.SmallFacts.bits_foldr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:42:13.9038+00:00
-- url     : https://prove2.me/theorems/5015c504-3242-4b32-a081-5f3db21dcf82
-- title:
--   Small Facts: bits foldr
-- statement:
--   A word that ends with 1 is the list of binary digits of a number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L107-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L107-L113

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

theorem CircuitLowerBound.SmallFacts.bits_foldr (w : List Bool) : Nat.bits ((w ++ [true]).foldr Nat.bit 0) = w ++ [true] := by sorry
