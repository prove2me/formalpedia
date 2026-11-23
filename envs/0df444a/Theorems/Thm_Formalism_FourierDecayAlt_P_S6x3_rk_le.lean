-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_le
-- name    : Formalism.FourierDecayAlt.P.S6x3.rk_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:29.119442+00:00
-- url     : https://prove2.me/theorems/3f1da093-04d2-44b0-a8c5-515fb10b162e
-- title:
--   S6x3: rk le
-- statement:
--   The S6x3 construction uses the rk le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L253-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L253-L261

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

theorem Formalism.FourierDecayAlt.P.S6x3.rk_le (A : FI E) (s : ℕ) : finrank ℤ (eig E A s) ≤ finrank ℤ (eig E A (s + 1)) := by sorry
