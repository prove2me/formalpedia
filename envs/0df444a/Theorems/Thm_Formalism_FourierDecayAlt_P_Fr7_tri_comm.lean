-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_tri_comm
-- name    : Formalism.FourierDecayAlt.P.Fr7.tri_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:43.378579+00:00
-- url     : https://prove2.me/theorems/d0b51f1c-053e-438f-98b2-35e356152e27
-- title:
--   Fr7: tri comm
-- statement:
--   The Fr7 construction uses the tri comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L68-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlusLetterFrameOfData.lean#L68-L90

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

theorem Formalism.FourierDecayAlt.P.Fr7.tri_comm {B : Type} [Ring B] [Algebra ℂ B] (b b' t t' e n : B) (D D' : ℂ)
    (hee : e * e = e) (hen : e * n = n) (hne : n * e = 0) (hnn : n * n = 0)
    (eb : e * b = b * e) (eb' : e * b' = b' * e) (et : e * t = t * e) (et' : e * t' = t' * e)
    (nb : n * b = b * n) (nb' : n * b' = b' * n) (nt : n * t = t * n) (nt' : n * t' = t' * n)
    (hbb : b * b' = b' * b)
    (K : (D - 1) • (b * t') + D' • (t * b') = (D' - 1) • (b' * t) + D • (t' * b)) :
    Commute (D • b - b * e - t * n) (D' • b' - b' * e - t' * n) := by sorry
