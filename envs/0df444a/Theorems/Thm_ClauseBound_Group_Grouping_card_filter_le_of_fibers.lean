-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_card_filter_le_of_fibers
-- name    : ClauseBound.Group.Grouping.card_filter_le_of_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:14.054882+00:00
-- url     : https://prove2.me/theorems/0698efe3-6864-4c2b-9ae7-f72dfc517868
-- title:
--   Grouping: card filter le of fibers
-- statement:
--   If all fibres of F over Xs have the same size, the fraction of Ω' on which F has a property is
--   the fraction of Xs with that property.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L78-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L78-L98

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

theorem ClauseBound.Group.Grouping.card_filter_le_of_fibers {Ω X : Type} [DecidableEq X] (Ω' : Finset Ω) (F : Ω → X) (Xs : Finset X) (hF : ∀ e ∈ Ω', F e ∈ Xs)
    (hconst : ∀ x ∈ Xs, ∀ x' ∈ Xs, #{e ∈ Ω' | F e = x} ≤ #{e ∈ Ω' | F e = x'}) (Q : X → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : (#{x ∈ Xs | Q x} : ℝ) ≤ ε * #Xs) : (#{e ∈ Ω' | Q (F e)} : ℝ) ≤ ε * #Ω' := by sorry
