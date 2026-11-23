-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x4_mem_idl
-- name    : Formalism.FourierDecayAlt.P.S6x4.mem_idl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:37.71656+00:00
-- url     : https://prove2.me/theorems/4f6b7cc4-8b90-4183-a01f-94bf9ad79288
-- title:
--   S6x4: mem idl
-- statement:
--   The S6x4 construction uses the mem idl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitPrimeToDifferent.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitPrimeToDifferent.lean#L20-L29

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

theorem Formalism.FourierDecayAlt.P.S6x4.mem_idl (E : Type) [Field E] [NumberField E] (g : ℕ) (k ν : ℤ) (t : E) (hg : 0 < g) :
    t ∈ idl E g k ν ↔ t / (g : E) ^ k ∈ dd E ^ ν := by sorry
