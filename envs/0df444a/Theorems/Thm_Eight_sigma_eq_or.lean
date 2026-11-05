-- Prove2me | Theorems.Thm_Eight_sigma_eq_or
-- name    : Eight.sigma_eq_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:21.924296+00:00
-- url     : https://prove2.me/theorems/0c8a3f37-7da5-4bd4-be72-866af61c349e
-- title:
--   Eight: sigma eq or
-- statement:
--   σ(p,q) is 1 or −1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L29-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L29-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.sigma_eq_or (p q : Block) : sigma p q = 1 ∨ sigma p q = -1 := by sorry
