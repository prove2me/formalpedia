-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Structure_lt_of_sum_lt
-- name    : ClauseBound.ParityChecks.Structure.lt_of_sum_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:36.868715+00:00
-- url     : https://prove2.me/theorems/29ca51d2-ef18-4a0d-af13-82e4e7dd3f99
-- title:
--   Structure: lt of sum lt
-- statement:
--   From (1/c)·S < 1, for a sum S of nonnegative terms a_i/b_i with 0 < b_i ≤ B: every a_i is below
--   c·B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L39-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L39-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Structure.lt_of_sum_lt {ι : Type} (s : Finset ι) (a b : ι → ℚ) (c B : ℚ) (hc : 0 < c) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i)
    (hB : ∀ i ∈ s, b i ≤ B) (h : 1 / c * ∑ i ∈ s, a i / b i < 1) {i : ι} (hi : i ∈ s) : a i < c * B := by sorry
