-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_isN_map
-- name    : Formalism.FourierDecayAlt.P.S3x8.isN_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:34.096031+00:00
-- url     : https://prove2.me/theorems/fec62c9c-77f2-43d4-9201-651cd642efd7
-- title:
--   S3x8: is N map
-- statement:
--   The S3x8 construction uses the is N map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L605-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L605-L614

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
variable {A : Type} {r k : ℕ}
variable [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x8.isN_map {B : Type} [CommRing B] (f : A →+* B) {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) :
    IsN (x.map f) := by sorry
