-- Prove2me | Theorems.Thm_Eight_exists_link_of_earlier
-- name    : Eight.exists_link_of_earlier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:35:42.788077+00:00
-- url     : https://prove2.me/theorems/3c05610a-0276-4b77-8319-66f951297466
-- title:
--   Eight: exists link of earlier
-- statement:
--   An occurrence with an earlier occurrence of the same variable is the second occurrence of a
--   test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L131-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L131-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
variable {Φ : Formula} {g μ k : ℕ}

theorem Eight.exists_link_of_earlier {p₀ q : Slot g μ k} (h1 : idx p₀ < idx q) (h2 : lab Φ p₀ = lab Φ q) (h3 : lab Φ q ≠ none) : ∃ p, Link Φ p q := by sorry
