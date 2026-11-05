-- Prove2me | Theorems.Thm_ClauseBound_Part_Upper_sum_mul_exp_le
-- name    : ClauseBound.Part.Upper.sum_mul_exp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:12.209272+00:00
-- url     : https://prove2.me/theorems/1d62da58-c15f-478c-b2df-401c70950737
-- title:
--   Upper: sum mul exp le
-- statement:
--   Σ_v v·e^{−yv} ≤ 1/y² over any finite set of v, for y > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L70-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Upper.lean#L70-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Upper

theorem ClauseBound.Part.Upper.sum_mul_exp_le {y : ℝ} (hy : 0 < y) (s : Finset ℕ) : ∑ v ∈ s, (v : ℝ) * Real.exp (-(y * v)) ≤ 1 / y ^ 2 := by sorry
