-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_det_of_cm
-- name    : Formalism.FourierDecayAlt.P.S3x8.det_of_cm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:28.5633+00:00
-- url     : https://prove2.me/theorems/a514b746-d6ad-4e9a-bfb5-93b3c5257352
-- title:
--   S3x8: det of cm
-- statement:
--   The S3x8 construction uses the det of cm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L192-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L192-L198

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]

theorem Formalism.FourierDecayAlt.P.S3x8.det_of_cm {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (h : IsUnit (cm X r le_rfl)) :
    IsUnit X.det := by sorry
