-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_blk_minus
-- name    : Formalism.FourierDecayAlt.P.Fr4.blk_minus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:11.938881+00:00
-- url     : https://prove2.me/theorems/8a4f572c-6228-4f9f-9fe5-8a3c5d00d251
-- title:
--   Fr4: blk minus
-- statement:
--   The Fr4 construction uses the blk minus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L96-L102

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr4
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Fr4.blk_minus (M : M2 (SlopeTestRemainingChoices S A)) (d : ℂ) (i j k l : Fin 2) :
    Formalism.YangianSpanCharacter.F.blk (((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A))) *
      E1 M) i j k l =
      (d - 1)⁻¹ • (d • (if k = l then M i j else 0) - (if i = k then M l j else 0)) := by sorry
