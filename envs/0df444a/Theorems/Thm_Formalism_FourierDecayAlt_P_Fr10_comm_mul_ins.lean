-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr10_comm_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Fr10.comm_mul_ins
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:00.061597+00:00
-- url     : https://prove2.me/theorems/d3d03e42-e8d3-48c1-b08d-ee348cb3ea80
-- title:
--   Fr10: comm mul ins
-- statement:
--   The Fr10 construction uses the comm mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinusLetterFrameOfData.lean#L103-L107

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

theorem Formalism.FourierDecayAlt.P.Fr10.comm_mul_ins {a : S} {u v : SlopeTestRemainingChoices S A} {M N : M2 (SlopeTestRemainingChoices S A)} (fu : FreeOf a u) (fv : FreeOf a v)
    (fM : FreeOf2 a M) (fN : FreeOf2 a N) (huv : Commute u v) (huN : ∀ i j, Commute u (N i j))
    (hvM : ∀ i j, Commute v (M i j)) (hMN : M * N = N * M) : Commute (u * ins a M) (v * ins a N) := by sorry
