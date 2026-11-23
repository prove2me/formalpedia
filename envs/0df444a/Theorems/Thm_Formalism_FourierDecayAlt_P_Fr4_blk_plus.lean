-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_blk_plus
-- name    : Formalism.FourierDecayAlt.P.Fr4.blk_plus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:58.12+00:00
-- url     : https://prove2.me/theorems/12b9efc5-5f87-4894-b21b-b3fe27a13666
-- title:
--   Fr4: blk plus
-- statement:
--   The Fr4 construction uses the blk plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L88-L94

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

theorem Formalism.FourierDecayAlt.P.Fr4.blk_plus (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) (i j k l : Fin 2) :
    Formalism.YangianSpanCharacter.F.blk (E1 M *
      ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)))) i j k l =
      (D - 1)⁻¹ • (D • (if k = l then M i j else 0) - (if k = j then M i l else 0)) := by sorry
