-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_corner_invariant
-- name    : Formalism.FourierDecayAlt.P.S3x7.corner_invariant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:40.426261+00:00
-- url     : https://prove2.me/theorems/fc7f2b95-1cfb-41a6-9cab-5b3bceb48247
-- title:
--   S3x7: corner invariant
-- statement:
--   The S3x7 construction uses the corner invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L83-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L83-L103

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

theorem Formalism.FourierDecayAlt.P.S3x7.corner_invariant {r : ℕ} {v₂ X v₁ : Matrix (Fin r) (Fin r) A} (h₂ : IsUpUni v₂) (h₁ : IsUpUni v₁)
    (l : ℕ) (hl : l ≤ r) : cm (v₂ * X * v₁) l hl = cm X l hl := by sorry
