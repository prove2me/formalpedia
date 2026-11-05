-- Prove2me | Theorems.Thm_CountKSatRate_Leaf_sat_leafM_iff
-- name    : CountKSatRate.Leaf.sat_leafM_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:40:17.0782+00:00
-- url     : https://prove2.me/theorems/a6c63282-2c59-493b-bb0c-9769b2145013
-- title:
--   Leaf: sat leaf M iff
-- statement:
--   An assignment satisfies `leafM x` exactly if it satisfies `leafF x`: the clauses left out are of
--   the form xᵢ ∨ ¬xᵢ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L52-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L52-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Leaf
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open PaddedDescent.F.Mark (occ nSat WfL)

theorem CountKSatRate.Leaf.sat_leafM_iff {n : ℕ} {x : CNode} (hs : ∀ C ∈ x.2, C ∈ taut n ∨ ∃ l, C = [l]) (a : ℕ → Bool) :
    (∀ C ∈ leafM x, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ C ∈ leafF x, ∃ l ∈ C, a l.1 = l.2 := by sorry
