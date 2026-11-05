-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_sum_words_eq
-- name    : ClauseBound.Alg.Enum.sum_words_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:06.586827+00:00
-- url     : https://prove2.me/theorems/28c54db1-3f85-409f-ae20-edf2ae0382ae
-- title:
--   Enum: sum words eq
-- statement:
--   A sum over all words of U/2 bits is a sum over these tuples: the entry at a place is the chunk
--   of that number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L164-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L164-L177

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
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}

theorem ClauseBound.Alg.Enum.sum_words_eq (g : ℕ) (F : FNet C) (c : C) (G : (Fin g × Fin g → List Bool) → ℤ) :
    ∑ w ∈ words (enumBits g F c), G (fun p => chunkAt (enumLen g F c) (pos p) w) =
      ∑ t ∈ tuples (fun _ : Fin g × Fin g => True) (fun p => words (enumLen g F c (pos p))) [], G t := by sorry
