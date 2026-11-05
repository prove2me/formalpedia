-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_tuples_eq
-- name    : ClauseBound.Alg.Enum.tuples_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:28.527819+00:00
-- url     : https://prove2.me/theorems/23e153d5-f9f8-402f-8e8b-a4a6f5af0bfc
-- title:
--   Enum: tuples eq
-- statement:
--   The labels of all pairs are the tuples that have a word of the length of the chunk at every
--   place.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L150-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L150-L160

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

theorem ClauseBound.Alg.Enum.tuples_eq (hN : F.toP.Presents c N 0 0) :
    tuples (fun p : Fin g × Fin g => p.1 < p.2) (fun p => N.lab p.1 p.2) [] =
      tuples (fun _ : Fin g × Fin g => True) (fun p => words (enumLen g F c (pos p))) [] := by sorry
