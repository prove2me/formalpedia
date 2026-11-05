-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_sum_v_ge
-- name    : ClauseBound.Part.Lower.sum_v_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:38.780759+00:00
-- url     : https://prove2.me/theorems/10fac0e9-a0bb-4356-a429-e7b8dd988d17
-- title:
--   Lower: sum v ge
-- statement:
--   Σ_{1 ≤ v ≤ n} v·e^{−yv}·(1 − η·v²) ≥ 1/y² − 1/4 − 486·η/y⁴ if 0 < y ≤ 2 and the terms with v > n
--   are not positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L188-L223
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L188-L223

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

theorem ClauseBound.Part.Lower.sum_v_ge {y η : ℝ} (hy : 0 < y) (hy2 : y ≤ 2) (hη : 0 ≤ η) (n : ℕ) (hn : 1 ≤ η * (n : ℝ) ^ 2) :
    1 / y ^ 2 - 1 / 4 - 486 * η / y ^ 4 ≤ ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(y * v)) * (1 - η * (v : ℝ) ^ 2) := by sorry
