-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_value_eq_sum_labels
-- name    : ClauseBound.Alg.Enum.value_eq_sum_labels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:44.349471+00:00
-- url     : https://prove2.me/theorems/4faeccb9-5ec1-4275-934a-74b5b1e101e1
-- title:
--   Enum: value eq sum labels
-- statement:
--   The value of a network is the sum, over all choices t of a label for every pair, of the product
--   over the nodes a of Σ_z W_a(z) ∏_{b ≠ a} f_ab(z, t_ab).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L38-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L38-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {J σ τ : Type} [Fintype J] [LinearOrder J]

theorem ClauseBound.Alg.Enum.value_eq_sum_labels (N : Network J σ τ) (t₀ : τ) :
    N.value = ∑ t ∈ tuples (fun p : J × J => p.1 < p.2) (fun p => N.lab p.1 p.2) t₀,
      ∏ a, ∑ z ∈ N.S a, N.W a z * ∏ b ∈ univ.erase a, N.f a b z (t (pr a b)) := by sorry
