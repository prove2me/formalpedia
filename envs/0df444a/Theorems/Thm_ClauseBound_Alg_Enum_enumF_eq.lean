-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_enumF_eq
-- name    : ClauseBound.Alg.Enum.enumF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:53.503951+00:00
-- url     : https://prove2.me/theorems/093c3ded-e1c1-4845-9b83-6a94fb1c12e9
-- title:
--   Enum: enum F eq
-- statement:
--   With a long enough pad the function is the sum of the terms over all words of U/2 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L207-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L207-L222

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}

theorem ClauseBound.Alg.Enum.enumF_eq (pad : U) (g : ℕ) (F : FNet C) (c : C) (hE : 2 ^ enumBits g F c ≤ pad.length)
    (hn : ∀ a < g, 2 ^ F.n c a ≤ pad.length) :
    enumF pad g F c = ∑ w ∈ words (enumBits g F c), term F c fun p : Fin g × Fin g => chunkAt (enumLen g F c) (pos p) w := by sorry
