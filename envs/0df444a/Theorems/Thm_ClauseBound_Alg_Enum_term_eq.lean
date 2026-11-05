-- Prove2me | Theorems.Thm_ClauseBound_Alg_Enum_term_eq
-- name    : ClauseBound.Alg.Enum.term_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:08.13906+00:00
-- url     : https://prove2.me/theorems/db16e7cc-b692-4996-953a-07bd94b7dfd5
-- title:
--   Enum: term eq
-- statement:
--   The Enum construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L183-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Enum.lean#L183-L204

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_Groundwork_SatNet_term_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}

theorem ClauseBound.Alg.Enum.term_eq (hN : F.toP.Presents c N 0 0) (t : Fin g × Fin g → List Bool)
    (ht : t ∈ tuples (fun p : Fin g × Fin g => p.1 < p.2) (fun p => N.lab p.1 p.2) []) :
    ∏ a, ∑ z ∈ N.S a, N.W a z * ∏ b ∈ univ.erase a, N.f a b z (t (pr a b)) = term F c t := by sorry
