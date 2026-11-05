-- Prove2me | Theorems.Thm_CountKSatRate_Brute_length_filter_satAt
-- name    : CountKSatRate.Brute.length_filter_satAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:35:17.193274+00:00
-- url     : https://prove2.me/theorems/9f14d918-ffa1-47eb-87da-66091109a46f
-- title:
--   Brute: length filter sat At
-- statement:
--   Among the numbers below 2^n, as many satisfy the formula as there are satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Brute.lean#L36-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Brute.lean#L36-L51

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
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Brute
open Groundwork Groundwork.Prog Groundwork.Decode CountKSat PaddedDescent PaddedDescent.F
open Sat3 (CNF)
open SatK (numSat binary)

theorem CountKSatRate.Brute.length_filter_satAt {n : ℕ} (φ : CNF n) : ((List.range (2 ^ n)).filter fun y => satAt (toN φ) y).length = numSat φ := by sorry
