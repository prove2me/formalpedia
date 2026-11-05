-- Prove2me | Theorems.Thm_Eight_SecNetworks_size_word
-- name    : Eight.SecNetworks.size_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:59:49.352342+00:00
-- url     : https://prove2.me/theorems/11c8a575-4343-4b35-9402-780c051e70dc
-- title:
--   Sec Networks: size word
-- statement:
--   The size of a string of n bits is 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L98-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L98-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Clique
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_size_word
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
open Stepped
variable {C : Type}

theorem Eight.SecNetworks.size_word (l : List Bool) : size l = 2 * l.length + 1 := by sorry
