-- Prove2me | Theorems.Thm_CountKSatRate_Pad_padMW_runs
-- name    : CountKSatRate.Pad.padMW_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:05.075706+00:00
-- url     : https://prove2.me/theorems/8e515e2d-73e0-427d-a9c6-79320a73f103
-- title:
--   Pad: pad MW runs
-- statement:
--   The padding machine ends after e x + 1 steps with w = B (x, pad of length 2^(e x)); its states
--   have size at most 2|x| + 2·2^(e x) + 2|w| + 5.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L86-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L86-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_CountKSatRate_Pad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Pad
open Groundwork PaddedDescent Turing
variable {e : List Bool → ℕ} {B : List Bool × List Unit → List Bool}

theorem CountKSatRate.Pad.padMW_runs (e : List Bool → ℕ) (B : List Bool × List Unit → List Bool) (x : List Bool) :
    (padMW e B).Runs x (e x + 1) (2 * x.length + 2 * 2 ^ e x + 3 + (2 * (B (x, pad (e x))).length + 2)) (B (x, pad (e x))) := by sorry
