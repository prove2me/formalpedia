-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_of_sub_one
-- name    : Formalism.FourierDecayAlt.P.S3x8.int_of_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:10.061416+00:00
-- url     : https://prove2.me/theorems/95d5a7b0-3f28-44f0-811b-d51821922fee
-- title:
--   S3x8: int of sub one
-- statement:
--   The S3x8 construction uses the int of sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L255-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L255-L258

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

theorem Formalism.FourierDecayAlt.P.S3x8.int_of_sub_one {m : Type} [DecidableEq m] {x : Matrix m m k0}
    (h : ∀ a b, (x - 1) a b ∈ (algebraMap o k0).toAddMonoidHom.range) : Integral o x := by sorry
