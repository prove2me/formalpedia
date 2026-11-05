-- Prove2me | Theorems.Thm_Eight_SecNetworks_length_thetaAt
-- name    : Eight.SecNetworks.length_thetaAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:26:44.722203+00:00
-- url     : https://prove2.me/theorems/45192899-fa2a-4e51-aa97-9d17137d36c6
-- title:
--   Sec Networks: length theta At
-- statement:
--   «θ_{a,b} ∈ {0,1}^{c_{a,b}}»: if a and b lie in different groups, the string Θ(χ(b)) has L bits
--   and Y_{γ,γ'} ≤ L for all pairs of groups, then θ_{a,b} has c_{a,b} bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L126-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L126-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Tables
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}

theorem Eight.SecNetworks.length_thetaAt (Np : NetworkProcedures C) {c : C} {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ} (hK0 : 0 < K) (hN : Paper.IsNetwork Np c N P B τ S)
    (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → (N.merge (grouping hK0 x) [] []).c γ γ' ≤ L) (Θ : Fin K → List Bool) {a b : Fin g}
    (hne : grouping hK0 x a ≠ grouping hK0 x b) (hΘ : (Θ (grouping hK0 x b)).length = L) : (thetaAt Np c hK0 x Θ a b).length = N.c a b := by sorry
