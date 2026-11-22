-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_mk_low
-- name    : Formalism.FourierDecayAlt.P.S3x7.mk_low
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:50.590056+00:00
-- url     : https://prove2.me/theorems/82fae76c-c991-455a-a97d-3e78238cf232
-- title:
--   S3x7: mk low
-- statement:
--   The S3x7 construction uses the mk low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L40-L42

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

theorem Formalism.FourierDecayAlt.P.S3x7.mk_low {r : ℕ} {L : Matrix (Fin r) (Fin r) A} (h : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) : IsLowUni L := by sorry
