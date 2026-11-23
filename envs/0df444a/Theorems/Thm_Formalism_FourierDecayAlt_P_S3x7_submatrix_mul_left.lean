-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_submatrix_mul_left
-- name    : Formalism.FourierDecayAlt.P.S3x7.submatrix_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:22.20086+00:00
-- url     : https://prove2.me/theorems/8c2650c8-3272-46bf-b065-7703b5e5eeea
-- title:
--   S3x7: submatrix mul left
-- statement:
--   The S3x7 construction uses the submatrix mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L14-L22

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

theorem Formalism.FourierDecayAlt.P.S3x7.submatrix_mul_left {l r : ℕ} {m : Type} (e : Fin l → Fin r) (he : Function.Injective e)
    (P M : Matrix (Fin r) (Fin r) A) (f : m → Fin r)
    (h : ∀ a k, k ∉ Set.range e → P (e a) k = 0) :
    (P * M).submatrix e f = P.submatrix e e * M.submatrix e f := by sorry
