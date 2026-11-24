-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_smul_matrix2_of
-- name    : Formalism.FourierDecayAlt.P.Fr9.smul_matrix2_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:04:43.268907+00:00
-- url     : https://prove2.me/theorems/9b4a91b3-58ba-4e58-8801-02c0dd59ba3a
-- title:
--   Fr9: smul matrix2 of
-- statement:
--   The Fr9 construction uses the smul matrix2 of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CommuteLevelZeroElement.lean#L261-L264

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Fr9.smul_matrix2_of {B : Type*} [Ring B] [Algebra ℂ B] (c : ℂ) (p q s t : B) :
    c • !![p, q; s, t] = !![c • p, c • q; c • s, c • t] := by sorry
