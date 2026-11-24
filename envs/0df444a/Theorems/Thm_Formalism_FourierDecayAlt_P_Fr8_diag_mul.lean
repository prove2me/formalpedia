-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_diag_mul
-- name    : Formalism.FourierDecayAlt.P.Fr8.diag_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:04:30.279307+00:00
-- url     : https://prove2.me/theorems/d3e32f1c-4ff4-462c-acda-401ae7f16b3c
-- title:
--   Fr8: diag mul
-- statement:
--   The Fr8 construction uses the diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L312-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussFormMinusLetter.lean#L312-L315

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8

theorem Formalism.FourierDecayAlt.P.Fr8.diag_mul {R : Type} [Ring R] (a b c d : R) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) R) * !![c, 0; 0, d] = !![a * c, 0; 0, b * d] := by sorry
