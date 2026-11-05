-- Prove2me | Theorems.Thm_ClauseBound_Boson_Half_factors
-- name    : ClauseBound.Boson.Half.factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:02.628297+00:00
-- url     : https://prove2.me/theorems/9b9ab8b3-72de-4a1d-a44a-1375db6c4329
-- title:
--   Half: factors
-- statement:
--   A function that is a sum over i ≤ 2h and over the monomials τ of weight t(i) of products of two
--   bounded factors factors through the number of the pairs (i, τ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L128-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Boson/Half.lean#L128-L140

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Definitions.Def_ClauseBound_Boson_Half
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Half

theorem ClauseBound.Boson.Half.factors {Z Z' : Type} {h : ℕ} (F : Z → Z' → ℤ) (t : ℕ → ℤ) (f : ℕ → Multiset ℕ → Z → ℤ) (f' : ℕ → Multiset ℕ → Z' → ℤ)
    (hF : ∀ z z', F z z' = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (t i), f i τ z * f' i τ z')
    (hf : ∀ i ∈ range (2 * h + 1), ∀ τ ∈ Pz (t i), ∀ z, |f i τ z| ≤ 2 ^ eL h)
    (hf' : ∀ i ∈ range (2 * h + 1), ∀ τ ∈ Pz (t i), ∀ z, |f' i τ z| ≤ 2 ^ eR h) :
    Pieces.FactorsThrough F (Nat.clog 2 (∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i))) (2 ^ big h) := by sorry
