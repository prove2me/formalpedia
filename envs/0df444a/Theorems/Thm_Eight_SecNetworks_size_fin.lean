-- Prove2me | Theorems.Thm_Eight_SecNetworks_size_fin
-- name    : Eight.SecNetworks.size_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:02:40.36906+00:00
-- url     : https://prove2.me/theorems/6d381afc-d765-4d7d-b47f-89738d8f0330
-- title:
--   Sec Networks: size fin
-- statement:
--   A node of [K] is not larger than K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L106-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L106-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
open Stepped
variable {C : Type}

theorem Eight.SecNetworks.size_fin {K : ℕ} (a : Fin K) : size a.val ≤ size K := by sorry
