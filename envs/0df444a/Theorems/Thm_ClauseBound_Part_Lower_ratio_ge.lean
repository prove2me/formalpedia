-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_ratio_ge
-- name    : ClauseBound.Part.Lower.ratio_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:27.340773+00:00
-- url     : https://prove2.me/theorems/b39bc3e5-cff3-47ec-9c4c-6d57c93752fb
-- title:
--   Lower: ratio ge
-- statement:
--   The comparison function exp(c√m)/m^B at m = s² − x against its value at s²: the quotient is at
--   least exp(−(c/(2s) − B/s²)·x)·(1 − c·x²/(2s³)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L66-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L66-L96

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

theorem ClauseBound.Part.Lower.ratio_ge {c s x : ℝ} (B : ℕ) (hc : 0 ≤ c) (hs : 0 < s) (hx : 0 ≤ x) (hxs : x < s ^ 2) :
    Real.exp (c * s) / (s ^ 2) ^ B * (Real.exp (-((c / (2 * s) - B / s ^ 2) * x)) * (1 - c / (2 * s ^ 3) * x ^ 2))
      ≤ Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B := by sorry
