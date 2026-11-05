-- Prove2me | Theorems.Thm_CountKSat_Value_value_wordNet_eq_cntN
-- name    : CountKSat.Value.value_wordNet_eq_cntN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:20:31.867709+00:00
-- url     : https://prove2.me/theorems/b8a3317a-5120-4bec-a676-80f2bff9a1ef
-- title:
--   Value: value word Net eq cnt N
-- statement:
--   The same for the network that the program builds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Value.lean#L71-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Value.lean#L71-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_CountKSat_Value
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.SatNet
open CountKSat.Value

theorem CountKSat.Value.value_wordNet_eq_cntN {g k n : ℕ} (hg : 0 < g) {x : Fml} (hk : ∀ C ∈ x, C.length ≤ k)
    (hlt : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) (hocc : ∀ i < n, ∃ C ∈ x, ∃ l ∈ C, l.1 = i) :
    (Count.wordNet g k x).value = cntN n x := by sorry
