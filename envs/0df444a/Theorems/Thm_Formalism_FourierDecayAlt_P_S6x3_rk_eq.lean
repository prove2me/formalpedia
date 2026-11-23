-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_rk_eq
-- name    : Formalism.FourierDecayAlt.P.S6x3.rk_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:24.449124+00:00
-- url     : https://prove2.me/theorems/efb49847-51b5-429d-889f-9b9ab2f316a3
-- title:
--   S6x3: rk eq
-- statement:
--   The S6x3 construction uses the rk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L309-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L309-L318

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

theorem Formalism.FourierDecayAlt.P.S6x3.rk_eq (A : FI E) (s : ℕ) (hA0 : A ≠ 0) (hA : ConjStable E A) :
    finrank ℤ (eig E A s) = deg E := by sorry
