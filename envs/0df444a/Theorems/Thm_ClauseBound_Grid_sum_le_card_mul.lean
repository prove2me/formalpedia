-- Prove2me | Theorems.Thm_ClauseBound_Grid_sum_le_card_mul
-- name    : ClauseBound.Grid.sum_le_card_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:52.277276+00:00
-- url     : https://prove2.me/theorems/085f83d5-5cc2-43e3-882d-8b56138d73d4
-- title:
--   Grid: sum le card mul
-- statement:
--   A sum of numbers that are at most c is at most their number times c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L58-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L58-L60

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

theorem ClauseBound.Grid.sum_le_card_mul {ι : Type} (s : Finset ι) (f : ι → ℕ) (c : ℕ) (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ #s * c := by sorry
