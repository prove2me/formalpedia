-- Prove2me | Theorems.Thm_ClauseBound_Grid_sum_erase_eq
-- name    : ClauseBound.Grid.sum_erase_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:57.246197+00:00
-- url     : https://prove2.me/theorems/cadee07e-5655-4f77-9db6-7d2cd204b37e
-- title:
--   Grid: sum erase eq
-- statement:
--   A sum over ordered pairs of distinct elements of a function of the unordered pair counts each
--   pair a < b twice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L81-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L81-L100

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

theorem ClauseBound.Grid.sum_erase_eq {X : Type} [Fintype X] [LinearOrder X] (h : X × X → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, h (min a b, max a b) = 2 * ∑ q ∈ pairs X, h q := by sorry
