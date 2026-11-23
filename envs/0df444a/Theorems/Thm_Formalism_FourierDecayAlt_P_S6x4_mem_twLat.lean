-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x4_mem_twLat
-- name    : Formalism.FourierDecayAlt.P.S6x4.mem_twLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:22.510465+00:00
-- url     : https://prove2.me/theorems/ed521a7f-3bef-4308-a031-28f883ac0933
-- title:
--   S6x4: mem tw Lat
-- statement:
--   The S6x4 construction uses the mem tw Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitPrimeToDifferent.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitPrimeToDifferent.lean#L9-L18

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitPrimeToDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x4
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem Formalism.FourierDecayAlt.P.S6x4.mem_twLat (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by sorry
