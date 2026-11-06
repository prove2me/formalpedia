-- Prove2me | Theorems.Thm_Eight_ViaGrouping_exponent_eq
-- name    : Eight.ViaGrouping.exponent_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:31.833408+00:00
-- url     : https://prove2.me/theorems/e61d3cec-9880-405e-aa3d-c805aee41aab
-- title:
--   Via Grouping: exponent eq
-- statement:
--   The exponent of `Correct` with ε = e and b = e + 2 is the exponent of Lemma 1: e·U + (e + 2)·gP/K =
--   e(U + gP/K) + 2gP/K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L297-L297
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L297-L297

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_SingleBitPieces_exponent_eq

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Cost

theorem Eight.ViaGrouping.exponent_eq (e U g P K : ℝ) : e * U + (e + 2) * (g * P) / K = e * (U + g * P / K) + 2 * (g * P) / K := by sorry
