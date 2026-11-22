-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_isUnit_det
-- name    : Formalism.FourierDecayAlt.P.S3x2.isN_isUnit_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:53:56.892796+00:00
-- url     : https://prove2.me/theorems/468c9a8c-64ca-47a6-b3b6-f23167511669
-- title:
--   S3x2: is N is Unit det
-- statement:
--   The S3x2 construction uses the is N is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L291-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L291-L292

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

theorem Formalism.FourierDecayAlt.P.S3x2.isN_isUnit_det {x : Matrix (Idx r k) (Idx r k) A} (hx : IsN x) : IsUnit x.det := by sorry
