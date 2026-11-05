-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_block_flatten
-- name    : CircuitLowerBound.Parse.block_flatten
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:49:48.460172+00:00
-- url     : https://prove2.me/theorems/1e23cc1b-fc8b-4719-a578-e0bc46ce6a26
-- title:
--   Parse: block flatten
-- statement:
--   The j-th block of a concatenation of words of length ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L81-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L81-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Parse

theorem CircuitLowerBound.Parse.block_flatten {ℓ : ℕ} : ∀ (L : List (List Bool)) (j : ℕ) (hj : j < L.length), (∀ w ∈ L, w.length = ℓ) → block ℓ j L.flatten = L[j]
  := by sorry
