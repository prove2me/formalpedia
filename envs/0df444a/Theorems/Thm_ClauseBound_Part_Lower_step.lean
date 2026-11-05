-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_step
-- name    : ClauseBound.Part.Lower.step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:28.089599+00:00
-- url     : https://prove2.me/theorems/d045afb9-c0b9-4892-85a7-56c36e629bcc
-- title:
--   Lower: step
-- statement:
--   If the bound holds below n, and √n ≥ 4B/c + c with B ≥ 3890, it holds at n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L344-L448
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L344-L448

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower

theorem ClauseBound.Part.Lower.step {H : ℝ} {B : ℕ} (hH : 0 ≤ H) (hB : (3890 : ℝ) ≤ B) {n : ℕ} (hn : 4 * (B : ℝ) / cHR + cHR ≤ Real.sqrt n)
    (ih : ∀ m, 1 ≤ m → m < n → H * Real.exp (cHR * Real.sqrt m) / (m : ℝ) ^ B ≤ p m) :
    H * Real.exp (cHR * Real.sqrt n) / (n : ℝ) ^ B ≤ p n := by sorry
