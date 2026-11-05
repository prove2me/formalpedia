-- Prove2me | Theorems.Thm_Eight_ViaGrouping_searchP_runs
-- name    : Eight.ViaGrouping.searchP_runs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:19.793048+00:00
-- url     : https://prove2.me/theorems/85b90d6f-cc7c-4236-9645-7abdbe686306
-- title:
--   Via Grouping: search P runs
-- statement:
--   The search, for any procedures and any context: 2·K^g steps, on states of size at most 4·(size
--   of c + size of K^g) + 10; the result is the first x < K^g to which the test says yes, if there is
--   one. Both bounds but for the size of c depend on K and g only: «(a constant)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L127-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L127-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.searchP_runs (K g : ℕ) (Np : Procs C) (c : C) :
    (searchP K g Np).Runs c (2 * K ^ g) (4 * (size c + size (K ^ g)) + 10) ((List.range (K ^ g)).find? fun x => goodP K g Np (c, x)) := by sorry
