-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_single_comm
-- name    : Formalism.FourierDecayAlt.P.JFxE.single_comm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:54:08.692181+00:00
-- url     : https://prove2.me/theorems/ec7334fe-bef3-4e0f-b723-affd2d817afd
-- title:
--   JFx E: single comm
-- statement:
--   The JFx E construction uses the single comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapAdInv.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapAdInv.lean#L60-L70

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapAdInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxE.single_comm (a b c d : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) : Mat k r) := by sorry
