-- Prove2me | Theorems.Thm_Eight_SecNetworks_place_lt
-- name    : Eight.SecNetworks.place_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:01:53.090688+00:00
-- url     : https://prove2.me/theorems/c6bc64c6-d9a4-476d-bf0c-3dc7bf9983ee
-- title:
--   Sec Networks: place lt
-- statement:
--   The places of the nodes other than w are below K − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L31-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Clique.lean#L31-L34

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

theorem Eight.SecNetworks.place_lt {K : ℕ} (w w' : Fin K) (h : w' ≠ w) : place w w' < K - 1 := by sorry
