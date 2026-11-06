-- Prove2me | Theorems.Thm_Eight_ViaGrouping_COUNTp_cost
-- name    : Eight.ViaGrouping.COUNTp_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:24:50.801516+00:00
-- url     : https://prove2.me/theorems/d0db7845-e9d8-4f83-97dc-f42880ed80a9
-- title:
--   Via Grouping: COUNTp cost
-- statement:
--   **Section 6, «Cost», for COUNT of Algorithm 1.** Let 0 < δ' ≤ 1. At every level ℓ with K_ℓ ≥
--   72/δ' and e_ℓ ≤ δ'/12, COUNT(Φ) returns the number of assignments of the variables occurring in Φ
--   that satisfy Φ within A·2^{δ'm} steps, on states of polynomial size.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L92-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L92-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.COUNTp_cost {δ' : ℝ} (hδ' : 0 < δ') (hδ'1 : δ' ≤ 1) {ℓ : ℕ} (hK : 72 / δ' ≤ levelK ℓ) (hE : Level.levelE ℓ ≤ δ' / 12) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, (COUNTp ℓ).Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by sorry
