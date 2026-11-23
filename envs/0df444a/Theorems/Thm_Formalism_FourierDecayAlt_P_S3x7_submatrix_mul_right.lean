-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_submatrix_mul_right
-- name    : Formalism.FourierDecayAlt.P.S3x7.submatrix_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:21.687196+00:00
-- url     : https://prove2.me/theorems/86c10ea7-37ca-4d77-bfdd-8851b8b0ab9f
-- title:
--   S3x7: submatrix mul right
-- statement:
--   The S3x7 construction uses the submatrix mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L24-L32

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

theorem Formalism.FourierDecayAlt.P.S3x7.submatrix_mul_right {l r : ℕ} {m : Type} (e : Fin l → Fin r) (he : Function.Injective e)
    (M P : Matrix (Fin r) (Fin r) A) (f : m → Fin r)
    (h : ∀ k b, k ∉ Set.range e → P k (e b) = 0) :
    (M * P).submatrix f e = M.submatrix f e * P.submatrix e e := by sorry
