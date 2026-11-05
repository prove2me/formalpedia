-- Prove2me | Theorems.Thm_CountKSatRate_Brute_outW_eq_binary
-- name    : CountKSatRate.Brute.outW_eq_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:51.483203+00:00
-- url     : https://prove2.me/theorems/c5448b28-ba1a-47f6-979d-a9d7221c53b0
-- title:
--   Brute: out W eq binary
-- statement:
--   `outW` writes N as n + 1 bits, lowest bit first, exactly as `binary n N`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Brute.lean#L54-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Brute.lean#L54-L56

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Brute
open Groundwork Groundwork.Prog Groundwork.Decode CountKSat PaddedDescent PaddedDescent.F
open Sat3 (CNF)
open SatK (numSat binary)

theorem CountKSatRate.Brute.outW_eq_binary (n : ℕ) (ψ : Fml) (N : ℕ) : outW ((List.replicate n (), ψ), N) = binary n N := by sorry
