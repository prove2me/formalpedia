-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_iff
-- name    : Formalism.FourierDecayAlt.P.S3x2.isN_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:22:45.971037+00:00
-- url     : https://prove2.me/theorems/2c7ae393-2740-4970-be77-64a23e89c975
-- title:
--   S3x2: is N iff
-- statement:
--   The S3x2 construction uses the is N iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L151-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L151-L202

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x2.isN_iff (x : Matrix (Idx r k) (Idx r k) A) : IsN x ↔ IsUc (cI r k) x := by sorry
