-- Prove2me | Theorems.Thm_Eight_SecNetworks_var_Y
-- name    : Eight.SecNetworks.var_Y
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:53:34.223301+00:00
-- url     : https://prove2.me/theorems/7cfe3c7b-f163-4a6f-ad5c-154f082ce53d
-- title:
--   Sec Networks: var Y
-- statement:
--   «Hence Var Y_{γ,γ'} ≤ Σ_{(a,b) : a ≠ b} c_{a,b}·4P = 4PU»: Σ_χ (Y − U/K²)² ≤ 4PU·K^g, multiplied
--   by K⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L150-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L150-L166

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

theorem Eight.SecNetworks.var_Y {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) {γ γ' : Fin K} (hne : γ ≠ γ') :
    ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2
      ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) * K ^ 4 * K ^ g : ℕ) : ℤ) := by sorry
