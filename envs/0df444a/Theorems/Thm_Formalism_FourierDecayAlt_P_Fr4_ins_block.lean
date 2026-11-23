-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_ins_block
-- name    : Formalism.FourierDecayAlt.P.Fr4.ins_block
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:32.671014+00:00
-- url     : https://prove2.me/theorems/cda666be-5ad3-4df4-bc0e-cd1d3fc4be75
-- title:
--   Fr4: ins block
-- statement:
--   The Fr4 construction uses the ins block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L120-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FreeOf2RmatrixTranspose.lean#L120-L129

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

theorem Formalism.FourierDecayAlt.P.Fr4.ins_block (a : S) (c D : ℂ) (x : SlopeTestRemainingChoices S A) (y : Fin 2 → SlopeTestRemainingChoices S A) (m : Fin 2) :
    ins a (Matrix.of fun k l => c • (D • (if k = l then x else 0) - (if k = m then y l else 0))) =
      c • (D • x - (eU a m 0 * y 0 + eU a m 1 * y 1)) := by sorry
