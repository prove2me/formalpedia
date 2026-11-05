-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_mem_cls
-- name    : ClauseBound.Group.Grouping.mem_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:21.297193+00:00
-- url     : https://prove2.me/theorems/12fb07ce-fd95-4ca1-9bc4-7d064d521fe0
-- title:
--   Grouping: mem cls
-- statement:
--   The Grouping construction uses the mem cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L110-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L110-L110

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

theorem ClauseBound.Group.Grouping.mem_cls {e : Equiv.Perm (Fin (K * n))} {γ : Fin K} {a : Fin (K * n)} : a ∈ cls e γ ↔ chi0 (e a) = γ := by sorry
