-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_freeOf2_matrix_entries
-- name    : Formalism.FourierDecayAlt.P.Fr4.freeOf2_matrix_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:47.950803+00:00
-- url     : https://prove2.me/theorems/93ee9b42-85b5-4c4e-bdfe-287fa5af96de
-- title:
--   Fr4: free Of2 matrix entries
-- statement:
--   The Fr4 construction uses the free Of2 matrix entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L58-L65

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

theorem Formalism.FourierDecayAlt.P.Fr4.freeOf2_matrix_entries {c : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) (hz : FreeOf c z)
    (hw : FreeOf c w) : FreeOf2 c !![x, y; z, w] := by sorry
