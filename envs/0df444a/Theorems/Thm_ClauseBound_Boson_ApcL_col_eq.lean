-- Prove2me | Theorems.Thm_ClauseBound_Boson_ApcL_col_eq
-- name    : ClauseBound.Boson.ApcL_col_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:34.36323+00:00
-- url     : https://prove2.me/theorems/680ab032-bd3c-4ab6-8811-36fdab9d1017
-- title:
--   Boson: Apc L col eq
-- statement:
--   The piece as a sum over i ≤ 2h and the monomials τ of weight 2h − s − i: one factor depends on
--   (x,u), the other on (y,v).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfList.lean#L40-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/HalfList.lean#L40-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Boson_HalfList
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
variable {lam h : ℕ}
variable {ℓ : Pieces.Bits lam → List ℕ}

theorem ClauseBound.Boson.ApcL_col_eq (hℓ : ∀ x, Pos (ℓ x) ∧ (ℓ x).sum = h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ApcL ℓ h s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (2 * h - s - i),
      topK (ℓ x) h i (s - h + i) (ℓ u : Multiset ℕ) τ * botK (ℓ v) h (h - s - i) τ (ℓ y : Multiset ℕ) := by sorry
