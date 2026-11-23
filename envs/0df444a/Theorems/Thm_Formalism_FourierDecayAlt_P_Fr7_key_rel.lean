-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_key_rel
-- name    : Formalism.FourierDecayAlt.P.Fr7.key_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:28.143248+00:00
-- url     : https://prove2.me/theorems/126913f3-4482-4f4e-8d2c-50bd10b613d2
-- title:
--   Fr7: key rel
-- statement:
--   The Fr7 construction uses the key rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L58-L66

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1

theorem Formalism.FourierDecayAlt.P.Fr7.key_rel {B : Type} [Ring B] [Algebra ℂ B] (b b' t t' : B) (Y Y' Ya : ℂ) (hne : Y ≠ Y')
    (H1 : (Y - Y') • (t * b' - b' * t) = t * b' - t' * b)
    (H2 : (Y' - Y) • (t' * b - b * t') = t' * b - t * b') :
    (Y - Ya - 1) • (b * t') + (Y' - Ya) • (t * b') = (Y' - Ya - 1) • (b' * t) + (Y - Ya) • (t' * b) := by sorry
