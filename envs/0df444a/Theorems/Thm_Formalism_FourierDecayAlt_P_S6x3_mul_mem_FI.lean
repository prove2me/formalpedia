-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mul_mem_FI
-- name    : Formalism.FourierDecayAlt.P.S6x3.mul_mem_FI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:51.673984+00:00
-- url     : https://prove2.me/theorems/aebc36d7-e760-42ec-a560-9852d61f4795
-- title:
--   S6x3: mul mem FI
-- statement:
--   The S6x3 construction uses the mul mem FI property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L127-L130

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem Formalism.FourierDecayAlt.P.S6x3.mul_mem_FI (A : FI E) (z : 𝓞 E) (t : E) (ht : t ∈ A) : (z : E) * t ∈ A := by sorry
