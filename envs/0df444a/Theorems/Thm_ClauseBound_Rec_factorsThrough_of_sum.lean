-- Prove2me | Theorems.Thm_ClauseBound_Rec_factorsThrough_of_sum
-- name    : ClauseBound.Rec.factorsThrough_of_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:17.532196+00:00
-- url     : https://prove2.me/theorems/fef4f173-31fe-4c79-b208-bd7af124eaa5
-- title:
--   Rec: factors Through of sum
-- statement:
--   A sum of at most 2^c products f_i(z)·f'_i(z'), all values below b in absolute value, factors
--   through c bits with the bound b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Number.lean#L25-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Number.lean#L25-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_Number
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces

theorem ClauseBound.Rec.factorsThrough_of_sum {Z Z' ι : Type} (S : Finset ι) (F : Z → Z' → ℤ) (f : ι → Z → ℤ) (f' : ι → Z' → ℤ) (b : ℤ) (c : ℕ)
    (hF : ∀ z z', F z z' = ∑ i ∈ S, f i z * f' i z') (hc : #S ≤ 2 ^ c) (hb : 0 < b)
    (hf : ∀ i ∈ S, ∀ z, |f i z| < b) (hf' : ∀ i ∈ S, ∀ z, |f' i z| < b) : FactorsThrough F c b := by sorry
