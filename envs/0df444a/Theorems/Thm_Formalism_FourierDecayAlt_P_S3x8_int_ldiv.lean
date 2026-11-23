-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_int_ldiv
-- name    : Formalism.FourierDecayAlt.P.S3x8.int_ldiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:43.867538+00:00
-- url     : https://prove2.me/theorems/b9115f6c-1a31-4df5-ae14-9a4ea2c90ce0
-- title:
--   S3x8: int ldiv
-- statement:
--   The S3x8 construction uses the int ldiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L722-L726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L722-L726

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
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x8.int_ldiv {m : Type} {Y : Matrix (Fin r) m k0} {X : Matrix (Fin r) (Fin r) o} (hX : IsUnit X.det)
    (h : Integral o (X.map (algebraMap o k0) * Y)) : Integral o Y := by sorry
