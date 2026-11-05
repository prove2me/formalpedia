-- Prove2me | Theorems.Thm_Enumerate_stops_and_stack
-- name    : Enumerate.stops_and_stack
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:11:28.245608+00:00
-- url     : https://prove2.me/theorems/b7fbaf1c-bc40-4cdd-b4d6-87647d353bad
-- title:
--   Enumerate: stops and stack
-- statement:
--   What `SparsificationLemma.stTreeG` says of the tree that the walk goes through, for τ ≥ 24: the
--   procedure has stopped at every leaf, and the stack is small. (Lemma 4: time 2^{εn} times a
--   polynomial in n.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L69-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Enumeration.lean#L69-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Enumerate_Defs
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_Enumerate_Enumeration
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo

theorem Enumerate.stops_and_stack {τ : ℕ} (hτ : 24 ≤ τ) (n : ℕ) (φ : PFml) (hφ : IsKCNF 3 n φ) :
    (∀ x ∈ leaves (rule τ) (depth τ n) (start n φ), rule τ x = none) ∧
    ∀ i, ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1.length ≤ depth τ n + 1 ∧
      ∀ x ∈ ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1,
        x.1.length ≤ φ.length * 2 ^ 3 ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by sorry
