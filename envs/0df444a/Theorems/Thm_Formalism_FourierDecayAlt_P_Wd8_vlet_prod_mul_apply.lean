-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_vlet_prod_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Wd8.vlet_prod_mul_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:23.2628+00:00
-- url     : https://prove2.me/theorems/ec7d5033-7604-4676-837d-262df1b8346a
-- title:
--   Wd8: vlet prod mul apply
-- statement:
--   The Wd8 construction uses the vlet prod mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L519-L532
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L519-L532

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd8.vlet_prod_mul_apply (sites : List (Site A)) (l : Letter K S) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((sites.map fun σ => (vlet σ l : SlopeTestRemainingChoices S A)).prod * B) x y =
      ∑ j, (sites.map (lm l)).prod (x l.intersection_update_fsHerm_neg_one) j * B (Function.update x l.intersection_update_fsHerm_neg_one j) y := by sorry
