-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_planeWaveVec
-- name    : Formalism.FourierDecayAlt.P.Wd11.planeWaveVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:28.931796+00:00
-- url     : https://prove2.me/theorems/ac0b94fd-29c8-4e64-805c-bf1a6799ecd0
-- title:
--   Wd11: plane Wave Vec
-- statement:
--   The Wd11 construction uses the plane Wave Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L363-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L363-L381

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

theorem Formalism.FourierDecayAlt.P.Wd11.planeWaveVec (σ : Site A) (f fi : A) (s : K) (w : List (Letter K S))
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    bT σ w * Vw f s w = io f * bT σ w := by sorry
