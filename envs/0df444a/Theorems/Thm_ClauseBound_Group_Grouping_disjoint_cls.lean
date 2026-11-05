-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_disjoint_cls
-- name    : ClauseBound.Group.Grouping.disjoint_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:24.090842+00:00
-- url     : https://prove2.me/theorems/59f9355f-5380-4c6f-b6dc-312cac3a0023
-- title:
--   Grouping: disjoint cls
-- statement:
--   Different groups are disjoint.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L125-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L125-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
variable {K n : ℕ}

theorem ClauseBound.Group.Grouping.disjoint_cls (e : Equiv.Perm (Fin (K * n))) {γ γ' : Fin K} (h : γ ≠ γ') : Disjoint (cls e γ) (cls e γ') := by sorry
