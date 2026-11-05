-- Prove2me | Theorems.Thm_CountKSatRate_Brute_satAt_toN
-- name    : CountKSatRate.Brute.satAt_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:41.526745+00:00
-- url     : https://prove2.me/theorems/7d3d5fa0-b027-46b8-9fa1-de6ab752942a
-- title:
--   Brute: sat At to N
-- statement:
--   Assignment number y satisfies the formula, with variables written as natural numbers, exactly
--   when its binary digits make a literal of every clause true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Brute.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Brute.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
import Batteries.Data.Nat.Lemmas
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_CountKSatRate_Brute
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Brute
open Groundwork Groundwork.Prog Groundwork.Decode CountKSat PaddedDescent PaddedDescent.F
open Sat3 (CNF)
open SatK (numSat binary)

theorem CountKSatRate.Brute.satAt_toN {n : ℕ} (φ : CNF n) (y : ℕ) : satAt (toN φ) y = true ↔ ∀ C ∈ φ, ∃ l ∈ C, y.testBit l.1 = l.2 := by sorry
