-- Prove2me | Theorems.Thm_ClauseBound_Grid_sum_erase_le
-- name    : ClauseBound.Grid.sum_erase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:57.109029+00:00
-- url     : https://prove2.me/theorems/fa6c6004-7f0d-4c51-a75e-4f7004e17a79
-- title:
--   Grid: sum erase le
-- statement:
--   A sum over the p − 1 other elements of numbers that are at most c is at most pc.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L73-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L73-L77

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

theorem ClauseBound.Grid.sum_erase_le {p c : ℕ} (X : Type) [Fintype X] [DecidableEq X] (hX : Fintype.card X = p) (F : X → ℕ)
    (hF : ∀ b, F b ≤ c) (a : X) : ∑ b ∈ univ.erase a, F b ≤ p * c := by sorry
