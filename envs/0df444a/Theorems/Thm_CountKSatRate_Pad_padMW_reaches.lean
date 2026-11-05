-- Prove2me | Theorems.Thm_CountKSatRate_Pad_padMW_reaches
-- name    : CountKSatRate.Pad.padMW_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:49.468009+00:00
-- url     : https://prove2.me/theorems/39d4d843-d7bf-454d-a6cf-8f0d5e0bbc72
-- title:
--   Pad: pad MW reaches
-- statement:
--   From the pad of length 2^k, k ≤ e x: the remaining doublings and the last step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L60-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Pad.lean#L60-L82

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

theorem CountKSatRate.Pad.padMW_reaches (x : List Bool) : ∀ (d k : ℕ), k + d = e x →
    (padMW e B).Reaches (2 * x.length + 2 * 2 ^ e x + 3 + (2 * (B (x, pad (e x))).length + 2)) (B (x, pad (e x))) (.inl (x, pad k)) (d + 1)
  := by sorry
