-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_card_colour
-- name    : ClauseBound.Group.Grouping.card_colour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:35.775164+00:00
-- url     : https://prove2.me/theorems/a332bdf5-5e4e-4eaa-9cfa-ee08f84cef41
-- title:
--   Grouping: card colour
-- statement:
--   The sizes of the four classes of the colouring by membership in two disjoint sets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L43-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L43-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping

theorem ClauseBound.Group.Grouping.card_colour {V : Type} [Fintype V] [DecidableEq V] (A B : Finset V) (h : Disjoint A B) (y : Bool × Bool) :
    #{x | (decide (x ∈ A), decide (x ∈ B)) = y} =
      if y.1 = true then (if y.2 = true then 0 else #A) else (if y.2 = true then #B else Fintype.card V - (#A + #B)) := by sorry
