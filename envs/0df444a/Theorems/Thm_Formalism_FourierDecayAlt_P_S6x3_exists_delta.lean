-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_exists_delta
-- name    : Formalism.FourierDecayAlt.P.S6x3.exists_delta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:11.431045+00:00
-- url     : https://prove2.me/theorems/2a70d450-270e-4d75-a871-befcdea39a3a
-- title:
--   S6x3: exists delta
-- statement:
--   The S6x3 construction uses the exists delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L230-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L230-L248

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

theorem Formalism.FourierDecayAlt.P.S6x3.exists_delta : ∃ δ : 𝓞 E, (δ : E) ≠ 0 ∧ complexConj E δ = -(δ : E) := by sorry
