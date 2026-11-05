-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_mem_cls_mul
-- name    : ClauseBound.Group.Grouping.mem_cls_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:44.701799+00:00
-- url     : https://prove2.me/theorems/2c49a284-dcb1-4f11-8f12-c2acf992435d
-- title:
--   Grouping: mem cls mul
-- statement:
--   The groups of χ₀∘e∘p are the preimages under p of the groups of χ₀∘e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L129-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L129-L130

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

theorem ClauseBound.Group.Grouping.mem_cls_mul {e p : Equiv.Perm (Fin (K * n))} {γ : Fin K} {a : Fin (K * n)} : a ∈ cls (e * p) γ ↔ p a ∈ cls e γ := by sorry
