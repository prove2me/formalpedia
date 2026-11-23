-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_ldu_unique
-- name    : Formalism.FourierDecayAlt.P.S3x7.ldu_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:05.307862+00:00
-- url     : https://prove2.me/theorems/73cdc6c8-43c3-4161-8571-5fd5d4d107bb
-- title:
--   S3x7: ldu unique
-- statement:
--   The S3x7 construction uses the ldu unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L122-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L122-L173

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

theorem Formalism.FourierDecayAlt.P.S3x7.ldu_unique {r : ℕ} {L U L' U' : Matrix (Fin r) (Fin r) A} {d d' : Fin r → A}
    (hL : IsLowUni L) (hU : IsUpUni U) (hL' : IsLowUni L') (hU' : IsUpUni U')
    (hd : lead (L * Matrix.diagonal d * U) r le_rfl ∈ nonZeroDivisors A)
    (e : L * Matrix.diagonal d * U = L' * Matrix.diagonal d' * U') : L = L' ∧ d = d' ∧ U = U' := by sorry
