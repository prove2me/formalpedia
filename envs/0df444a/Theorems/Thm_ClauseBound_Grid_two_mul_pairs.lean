-- Prove2me | Theorems.Thm_ClauseBound_Grid_two_mul_pairs
-- name    : ClauseBound.Grid.two_mul_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:47.992061+00:00
-- url     : https://prove2.me/theorems/2e266f30-e82d-4219-9eb0-799e1348ba29
-- title:
--   Grid: two mul pairs
-- statement:
--   Twice the number of pairs a < b of a set of n elements is n(n−1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L63-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L63-L65

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

theorem ClauseBound.Grid.two_mul_pairs (X : Type) [Fintype X] [LinearOrder X] :
    2 * #(pairs X) = Fintype.card X * (Fintype.card X - 1) := by sorry
