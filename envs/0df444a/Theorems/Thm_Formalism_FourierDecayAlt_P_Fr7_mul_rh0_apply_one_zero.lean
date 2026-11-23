-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_mul_rh0_apply_one_zero
-- name    : Formalism.FourierDecayAlt.P.Fr7.mul_rh0_apply_one_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:51.718592+00:00
-- url     : https://prove2.me/theorems/d31db09a-ae7c-41fa-8bba-abd04c7b277a
-- title:
--   Fr7: mul rh0 apply one zero
-- statement:
--   The Fr7 construction uses the mul rh0 apply one zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L184-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L184-L190

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}

theorem Formalism.FourierDecayAlt.P.Fr7.mul_rh0_apply_one_zero (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) 1 0 = (D - 1)⁻¹ • (D • M 1 0 - M 1 0 * eU a 0 0 - M 1 1 * eU a 0 1) := by sorry
