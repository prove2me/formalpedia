-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_isNetwork
-- name    : Eight.ViaGrouping.Table.isNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:19:53.811798+00:00
-- url     : https://prove2.me/theorems/b3cc5eee-fcdc-4e18-a77b-7899f5f48ad9
-- title:
--   Table: is Network
-- statement:
--   A network in the sense of `IsNetworkP` is a network in the sense of Definition 2 once the
--   procedures are told B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L60-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]

theorem Eight.ViaGrouping.Table.isNetwork (h : IsNetworkP Np c N P B τ S) : IsNetwork { Np with B := fun _ => B } c N P B τ S := by sorry
