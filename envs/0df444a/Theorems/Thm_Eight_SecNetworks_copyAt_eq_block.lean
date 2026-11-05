-- Prove2me | Theorems.Thm_Eight_SecNetworks_copyAt_eq_block
-- name    : Eight.SecNetworks.copyAt_eq_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:02:52.833464+00:00
-- url     : https://prove2.me/theorems/6f701c33-58ea-4d69-8fd2-87c5bf3f9a60
-- title:
--   Sec Networks: copy At eq block
-- statement:
--   z_w(w') is the block number `place w w'` of the λ-bit blocks of z_w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L28-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L28-L28

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

theorem Eight.SecNetworks.copyAt_eq_block (lam w w' : ℕ) (z : List Bool) : copyAt lam w w' z = block lam (place w w') z := by sorry
