-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_mul_rmatrix_apply
-- name    : Formalism.FourierDecayAlt.P.Fr4.mul_rmatrix_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:14.358342+00:00
-- url     : https://prove2.me/theorems/4fd3bb3b-ebc8-40bb-a7ea-6e1153fabf50
-- title:
--   Fr4: mul rmatrix apply
-- statement:
--   The Fr4 construction uses the mul rmatrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L104-L110

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

theorem Formalism.FourierDecayAlt.P.Fr4.mul_rmatrix_apply (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) (i j : Fin 2) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • M i j - (M i 0 * eU a j 0 + M i 1 * eU a j 1)) := by sorry
