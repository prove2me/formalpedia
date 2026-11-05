-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_serves_Bp
-- name    : Eight.ViaGrouping.Cost.serves_Bp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:31.28205+00:00
-- url     : https://prove2.me/theorems/44ff8c70-51c5-41dd-976c-577c68af6747
-- title:
--   Cost: serves Bp
-- statement:
--   «So |W̃_γ| < 2^{B'} with B' = ⌈2gP/K⌉ + g²B»: query access with the bound 2^{P·⌊2g/K⌋ + g²B} on
--   the entries is query access with the bound 2^{B'}. Different from the paper: «at most» for «below».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L187-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L187-L189

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g : ℕ} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.Cost.serves_Bp {D : Type} {R : Stepped (D × IQ) ℤ} {d : D} {K : ℕ} {L t S' : ℕ} {W : Paper.Tables K} (g P B : ℕ)
    (h : ServesInst R d L (P * (2 * g / K) + g ^ 2 * B) t S' W) : ServesInst R d L (Bp K g P B) t S' W := by sorry
