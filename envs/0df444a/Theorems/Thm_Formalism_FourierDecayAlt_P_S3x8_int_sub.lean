-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_sub
-- name    : Formalism.FourierDecayAlt.P.S3x8.int_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:25.416306+00:00
-- url     : https://prove2.me/theorems/4fe17407-3b92-4c63-b8fd-22a25fe8f373
-- title:
--   S3x8: int sub
-- statement:
--   The S3x8 construction uses the int sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L238-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L238-L242

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

theorem Formalism.FourierDecayAlt.P.S3x8.int_sub {m n : Type} {x y : Matrix m n k0}
    (hx : Integral o x) (hy : Integral o y) : Integral o (x - y) := by sorry
