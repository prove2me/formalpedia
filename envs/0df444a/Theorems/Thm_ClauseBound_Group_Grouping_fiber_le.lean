-- Prove2me | Theorems.Thm_ClauseBound_Group_Grouping_fiber_le
-- name    : ClauseBound.Group.Grouping.fiber_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:36.860623+00:00
-- url     : https://prove2.me/theorems/899790e0-6885-42cd-94d9-25298837d34e
-- title:
--   Grouping: fiber le
-- statement:
--   If p carries A'' to A' and multiplication by p keeps Ω', then the group number γ' is A'' at
--   least as often on Ω' as it is A'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L134-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Group/Grouping.lean#L134-L140

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
variable {K n : ℕ}

theorem ClauseBound.Group.Grouping.fiber_le (Ω' : Finset (Equiv.Perm (Fin (K * n)))) (p : Equiv.Perm (Fin (K * n))) (hΩ : ∀ e ∈ Ω', e * p ∈ Ω') (γ' : Fin K)
    (A' A'' : Finset (Fin (K * n))) (hp : ∀ x, p x ∈ A' ↔ x ∈ A'') : #{e ∈ Ω' | cls e γ' = A'} ≤ #{e ∈ Ω' | cls e γ' = A''} := by sorry
