-- Prove2me | Theorems.Thm_Eight_SecNetworks_thetaAt_comm
-- name    : Eight.SecNetworks.thetaAt_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:39:22.305192+00:00
-- url     : https://prove2.me/theorems/72b49d34-948c-46a7-89dd-0a5d38cee164
-- title:
--   Sec Networks: theta At comm
-- statement:
--   «The two copies of the string on an edge {γ, γ'} must agree, and both W̃_γ and W̃_γ' read
--   θ_{a,b} from the same block of this string, so θ_{a,b} = θ_{b,a}»: if a and b lie in different
--   groups and the argument Θ of the table of a's group
--   and the argument Θ' of the table of b's group have the same string on the edge between the two
--   groups, then θ_{a,b}, read from Θ, is θ_{b,a}, read from Θ'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L116-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L116-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Tables
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}

theorem Eight.SecNetworks.thetaAt_comm (Np : NetworkProcedures C) (c : C) (hK0 : 0 < K) (x : ℕ) (Θ Θ' : Fin K → List Bool) {a b : Fin g} (hne : grouping hK0 x a ≠ grouping hK0 x b)
    (h : Θ (grouping hK0 x b) = Θ' (grouping hK0 x a)) : thetaAt Np c hK0 x Θ a b = thetaAt Np c hK0 x Θ' b a := by sorry
