-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_exists_perm_sets
-- name    : ClauseBound.Group.Grouping.exists_perm_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:15.235766+00:00
-- url     : https://prove2.me/theorems/c9e5b207-1d12-4b6c-8ec6-6af072af7560
-- title:
--   Grouping: exists perm sets
-- statement:
--   A permutation that keeps the set A and carries A'' to A', two sets of the same size that are
--   disjoint from A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L64-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L64-L72

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

theorem ClauseBound.Group.Grouping.exists_perm_sets {V : Type} [Fintype V] [DecidableEq V] (A A' A'' : Finset V) (h' : Disjoint A A') (h'' : Disjoint A A'') (hc : #A' = #A'') :
    ∃ p : Equiv.Perm V, (∀ x, p x ∈ A ↔ x ∈ A) ∧ ∀ x, p x ∈ A' ↔ x ∈ A'' := by sorry
