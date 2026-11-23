-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_diagonal
-- name    : Formalism.FourierDecayAlt.P.S3x7.border_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:15.575998+00:00
-- url     : https://prove2.me/theorems/b21b8b26-25e5-43b4-9f45-63abfdbaeb36
-- title:
--   S3x7: border diagonal
-- statement:
--   The S3x7 construction uses the border diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L218-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L218-L222

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

theorem Formalism.FourierDecayAlt.P.S3x7.border_diagonal {r : ℕ} (d : Fin r → A) (s : A) :
    Matrix.diagonal (Fin.snoc (α := fun _ => A) d s) = border (Matrix.diagonal d) 0 0 s := by sorry
