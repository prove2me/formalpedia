-- Prove2me | Theorems.Thm_CountKSatRate_Leaf_spec
-- name    : CountKSatRate.Leaf.spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:30:12.692221+00:00
-- url     : https://prove2.me/theorems/0c08135e-f1f1-4af6-8928-5819a5cc73aa
-- title:
--   Leaf: spec
-- statement:
--   What `PaddedDescent.F.StCountM` asks of a formula holds of `leafM x`, and its count is that of
--   `leafF x`. The hypotheses are what `StTreeK` says of a leaf.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L71-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Leaf.lean#L71-L90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Leaf
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open PaddedDescent.F.Mark (occ nSat WfL)

theorem CountKSatRate.Leaf.spec {k n c : ℕ} {x : CNode} (hk : 1 ≤ k) (h1 : ∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n)
    (ho : ∀ v, (occ x.1 v).length ≤ c) (hs : ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) :
    (leafM x).length ≤ (leafF x).length ∧ WfL k n [leafM x] ∧ (∀ v, (occ (leafM x) v).length ≤ c + 2) ∧ nSat n (leafM x) = cntN n (leafF x) := by sorry
