-- Prove2me | Theorems.Thm_Eight_SecNetworks_place_inj
-- name    : Eight.SecNetworks.place_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:20:25.5266+00:00
-- url     : https://prove2.me/theorems/79473448-a5d0-4de4-b60d-ece72c549c3a
-- title:
--   Sec Networks: place inj
-- statement:
--   Two nodes other than w have different places.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L37-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L37-L42

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

theorem Eight.SecNetworks.place_inj {K : ℕ} (w a b : Fin K) (ha : a ≠ w) (hb : b ≠ w) (h : place w a = place w b) : a = b := by sorry
