-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_bt_of_isNU
-- name    : Formalism.FourierDecayAlt.P.S3x8.bt_of_isNU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:46.15864+00:00
-- url     : https://prove2.me/theorems/dd714cfb-613d-4f9b-8bfc-203b06f1793b
-- title:
--   S3x8: bt of is NU
-- statement:
--   The S3x8 construction uses the bt of is NU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L592-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L592-L603

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

theorem Formalism.FourierDecayAlt.P.S3x8.bt_of_isNU {x : Matrix (Idx r k) (Idx r k) A} (hx : IsNU x) : BT x := by sorry
