-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_finrank_zsub
-- name    : Formalism.FourierDecayAlt.P.S6x3.finrank_zsub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:35.585347+00:00
-- url     : https://prove2.me/theorems/fd31f0cc-398f-4327-b7ed-2b0901a49d30
-- title:
--   S6x3: finrank zsub
-- statement:
--   The S6x3 construction uses the finrank zsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L196-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L196-L199

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

theorem Formalism.FourierDecayAlt.P.S6x3.finrank_zsub (A : FI E) (hA : A ≠ 0) : finrank ℤ (zsub E A) = finrank ℚ E := by sorry
