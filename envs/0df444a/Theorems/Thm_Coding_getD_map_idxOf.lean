-- Prove2me | Theorems.Thm_Coding_getD_map_idxOf
-- name    : Coding.getD_map_idxOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:10.366669+00:00
-- url     : https://prove2.me/theorems/c0aa28fd-ad99-4ee0-babf-cfd1dd1d14ca
-- title:
--   Coding: get D map idx Of
-- statement:
--   A list of values, read at the position of a member.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L72-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L72-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}

theorem Coding.getD_map_idxOf {α : Type} [BEq α] [LawfulBEq α] (f : α → Bool) {l : List α} {x : α} (hx : x ∈ l) : (l.map f).getD (l.idxOf x) false = f x := by sorry
