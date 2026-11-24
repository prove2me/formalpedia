-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_planeWaveWord
-- name    : Formalism.FourierDecayAlt.P.Wd11.planeWaveWord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:14.010062+00:00
-- url     : https://prove2.me/theorems/5238c862-822b-4e53-a735-28c260ea6aeb
-- title:
--   Wd11: plane Wave Word
-- statement:
--   The Wd11 construction uses the plane Wave Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L572-L613
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteTransposedRMatrix.lean#L572-L613

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

theorem Formalism.FourierDecayAlt.P.Wd11.planeWaveWord (QQ : K → M2 A) (f fi : A) (s : K) (w : List (Letter K S))
    (hW : IsWave f fi) (hQ : WaveQQ QQ f fi s) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    Vw f s w * Viw fi s w = 1 ∧ Viw fi s w * Vw f s w = 1 ∧
    star (Vw f s w) * RRw QQ w * Vw f s w = RRw QQ w ∧
    ∀ Y, d0 (Viw fi s w) * TTw QQ w Y * d0 (Vw f s w) =
      lift0 (Um (A := A) s)ᴴ * TTw QQ w Y * lift0 (Um (A := A) s) := by sorry
