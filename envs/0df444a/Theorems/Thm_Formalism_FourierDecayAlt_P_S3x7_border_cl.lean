-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
-- name    : Formalism.FourierDecayAlt.P.S3x7.border_cl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:05.036503+00:00
-- url     : https://prove2.me/theorems/e1f049b7-df43-4dcb-8df2-38f7112ef2fd
-- title:
--   S3x7: border cl
-- statement:
--   The S3x7 construction uses the border cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L191-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L191-L193

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x7.border_cl {r : ℕ} (B : Matrix (Fin r) (Fin r) A) (v u : Fin r → A)
    (c : A) (i : Fin r) : border B v u c i.castSucc (Fin.last r) = v i := by sorry
