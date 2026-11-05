-- Prove2me | Theorems.Thm_ClauseBound_Grid_abs_prod_le_pow
-- name    : ClauseBound.Grid.abs_prod_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:48.201889+00:00
-- url     : https://prove2.me/theorems/2e9cf31d-72c2-42f1-89b1-78b68f707cc7
-- title:
--   Grid: abs prod le pow
-- statement:
--   A product of integers of absolute value at most 2^B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L41-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L41-L45

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

theorem ClauseBound.Grid.abs_prod_le_pow {ι : Type} (s : Finset ι) (f : ι → ℤ) (B : ℕ) (h : ∀ i ∈ s, |f i| ≤ 2 ^ B) :
    |∏ i ∈ s, f i| ≤ 2 ^ (#s * B) := by sorry
