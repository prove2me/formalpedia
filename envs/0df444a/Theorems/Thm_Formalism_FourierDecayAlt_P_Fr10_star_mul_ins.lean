-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_star_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Fr10.star_mul_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:10.492323+00:00
-- url     : https://prove2.me/theorems/f7f329f2-6012-47b3-a2ba-019f30ecfaf0
-- title:
--   Fr10: star mul ins
-- statement:
--   The Fr10 construction uses the star mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L121-L123

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr10.star_mul_ins {a : S} {u : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (fu : FreeOf a u) (fM : FreeOf2 a M)
    (hu : star u = u) (hc : ∀ i j, Commute u (M i j)) (hM : Mᴴ = M) : star (u * ins a M) = u * ins a M := by sorry
