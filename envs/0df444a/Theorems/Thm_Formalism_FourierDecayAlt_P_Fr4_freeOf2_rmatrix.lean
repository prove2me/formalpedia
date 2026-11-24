-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_freeOf2_rmatrix
-- name    : Formalism.FourierDecayAlt.P.Fr4.freeOf2_rmatrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:07.076808+00:00
-- url     : https://prove2.me/theorems/f8127a5c-e68b-4088-bd34-6e42487a9d6d
-- title:
--   Fr4: free Of2 rmatrix
-- statement:
--   The Fr4 construction uses the free Of2 rmatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L73-L77

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

theorem Formalism.FourierDecayAlt.P.Fr4.freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by sorry
