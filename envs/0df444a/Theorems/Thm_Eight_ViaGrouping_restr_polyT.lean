-- Prove2me | Theorems.Thm_Eight_ViaGrouping_restr_polyT
-- name    : Eight.ViaGrouping.restr_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:33:40.870972+00:00
-- url     : https://prove2.me/theorems/c3757804-62db-415c-b816-3dd96a6a45db
-- title:
--   Via Grouping: restr poly T
-- statement:
--   The Via Grouping construction uses the restr poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L76-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/SatPsi.lean#L76-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsiDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_ToTuring_Poly_Count
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight.SecNetworks
variable {g k : ℕ} {Φ : Fml}

theorem Eight.ViaGrouping.restr_polyT {α : Type} [Enc α] (g k : ℕ) {φ : α → Fml} {a b : α → ℕ} {z : α → List Bool} (hφ : PolyT φ) (ha : PolyT a) (hb : PolyT b) (hz : PolyT z) :
    PolyT fun x => restr g k (φ x) (a x) (b x) (z x) := by sorry
