-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_vlet_wave
-- name    : Formalism.FourierDecayAlt.P.Wd11.vlet_wave
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:12.684661+00:00
-- url     : https://prove2.me/theorems/f3e3dd39-1813-468c-84cb-d59ff3f7e9cc
-- title:
--   Wd11: vlet wave
-- statement:
--   The Wd11 construction uses the vlet wave property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L346-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L346-L353

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd11.vlet_wave (σ : Site A) (f fi : A) (s : K) (l : Letter K S)
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) :
    vlet σ l * (io f * ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s)))) =
      io f * vlet σ l := by sorry
