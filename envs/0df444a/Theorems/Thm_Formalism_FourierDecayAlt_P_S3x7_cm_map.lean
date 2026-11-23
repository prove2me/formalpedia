-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_cm_map
-- name    : Formalism.FourierDecayAlt.P.S3x7.cm_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:01.610775+00:00
-- url     : https://prove2.me/theorems/f3b66e5e-0293-4c2a-900b-92a1092cac7d
-- title:
--   S3x7: cm map
-- statement:
--   The S3x7 construction uses the cm map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L375-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L375-L379

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
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x7.cm_map {B : Type} [CommRing B] (f : A →+* B) (X : Matrix (Fin r) (Fin r) A) (l : ℕ)
    (hl : l ≤ r) : f (cm X l hl) = cm (X.map f) l hl := by sorry
