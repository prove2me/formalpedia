-- Prove2me | Theorems.Thm_Eight_SecNetworks_cov_disjoint
-- name    : Eight.SecNetworks.cov_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:52:47.800195+00:00
-- url     : https://prove2.me/theorems/c3f16376-90b2-4690-b2c8-e736ac12ecd0
-- title:
--   Sec Networks: cov disjoint
-- statement:
--   «The indicators of two ordered pairs have covariance 0 if the pairs are disjoint»: both pairs
--   contribute with probability 1/K⁴ = (1/K²)·(1/K²). («and at most 1 otherwise» needs no proof:
--   indicators are at most 1.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L128-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L128-L130

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}

theorem Eight.SecNetworks.cov_disjoint {a b a' b' : Fin g} (hab : a ≠ b) (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b') (h5 : a' ≠ b') (γ γ' : Fin K) :
    #{χ : Fin g → Fin K | (χ a = γ ∧ χ b = γ') ∧ (χ a' = γ ∧ χ b' = γ')} * K ^ 4 = K ^ g := by sorry
