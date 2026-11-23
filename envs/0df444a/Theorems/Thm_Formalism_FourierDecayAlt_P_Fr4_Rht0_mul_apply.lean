-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_Rht0_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Fr4.Rht0_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:05.268805+00:00
-- url     : https://prove2.me/theorems/76e050ca-e39b-4ff5-bef9-ba7375a5500b
-- title:
--   Fr4: Rht0 mul apply
-- statement:
--   The Fr4 construction uses the Rht0 mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L112-L118

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

theorem Formalism.FourierDecayAlt.P.Fr4.Rht0_mul_apply (b : S) (M : M2 (SlopeTestRemainingChoices S A)) (d : ℂ) (i j : Fin 2) :
    (Rht0 b d * M : M2 (SlopeTestRemainingChoices S A)) i j =
      (d - 1)⁻¹ • (d • M i j - (eU b i 0 * M 0 j + eU b i 1 * M 1 j)) := by sorry
