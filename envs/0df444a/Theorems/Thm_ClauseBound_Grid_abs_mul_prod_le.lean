-- Prove2me | Theorems.Thm_ClauseBound_Grid_abs_mul_prod_le
-- name    : ClauseBound.Grid.abs_mul_prod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:23.36559+00:00
-- url     : https://prove2.me/theorems/4de4c76e-1482-4b22-af5e-426b6b7f2b16
-- title:
--   Grid: abs mul prod le
-- statement:
--   Factors 0, ±1 times factors of absolute value at most 2^b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L48-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L48-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid

theorem ClauseBound.Grid.abs_mul_prod_le {ι κ : Type} (s : Finset ι) (e : ι → ℤ) (t : Finset κ) (f : κ → ℤ) {b n : ℕ}
    (he : ∀ i, |e i| ≤ 1) (hf : ∀ k, |f k| ≤ 2 ^ b) (hn : #t * b ≤ n) :
    |(∏ i ∈ s, e i) * ∏ k ∈ t, f k| ≤ 2 ^ n := by sorry
