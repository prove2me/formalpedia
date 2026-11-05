-- Prove2me | Theorems.Thm_Eight_SecNetworks_size_ite_le
-- name    : Eight.SecNetworks.size_ite_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:20:27.997305+00:00
-- url     : https://prove2.me/theorems/6a4b8a7f-4b6d-4fe1-b91d-81c2458e36e0
-- title:
--   Sec Networks: size ite le
-- statement:
--   The numbers 0 and 1 have size at most 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L111-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L111-L112

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

theorem Eight.SecNetworks.size_ite_le (p : Prop) [Decidable p] : size (if p then (1 : ℤ) else 0) ≤ 2 := by sorry
