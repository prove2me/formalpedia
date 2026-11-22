-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_map
-- name    : Formalism.FourierDecayAlt.P.S3x8.int_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:30.797796+00:00
-- url     : https://prove2.me/theorems/1fb7edb4-5779-416e-ad1f-c99ceb95d677
-- title:
--   S3x8: int map
-- statement:
--   The S3x8 construction uses the int map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L224-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L224-L224

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
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]

theorem Formalism.FourierDecayAlt.P.S3x8.int_map {m n : Type} (y : Matrix m n o) : Integral o (y.map (algebraMap o k0)) := by sorry
