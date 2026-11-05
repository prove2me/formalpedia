-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_step_arith
-- name    : ClauseBound.Part.Lower.step_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:59.122687+00:00
-- url     : https://prove2.me/theorems/e9891e84-1377-45a0-be3e-d1e8efbf1a97
-- title:
--   Lower: step arith
-- statement:
--   With s = √n, α = c/(2s) − B/s², γ = c/(2s³), c² = 4Z and 1/α ≤ K ≤ 1/α + 1, the lower bound for
--   the double sum is at least n, if B ≥ 3890 and s ≥ 4B/c + c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L275-L329
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L275-L329

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

theorem ClauseBound.Part.Lower.step_arith {c s B α γ Z : ℝ} {K : ℕ} (hc : 0 < c) (hB : 3890 ≤ B) (hs : 4 * B / c + c ≤ s) (hα : α = c / (2 * s) - B / s ^ 2)
    (hγ : γ = c / (2 * s ^ 3)) (hZ : Z = c ^ 2 / 4) (hK1 : 1 / α ≤ K) (hK2 : (K : ℝ) ≤ 1 / α + 1) :
    s ^ 2 ≤ 1 / α ^ 2 * (Z - 1 / K) - K / 4 - 486 * γ / α ^ 4 * Z := by sorry
