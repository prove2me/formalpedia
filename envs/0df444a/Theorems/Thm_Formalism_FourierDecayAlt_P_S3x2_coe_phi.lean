-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
-- name    : Formalism.FourierDecayAlt.P.S3x2.coe_phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:47.981796+00:00
-- url     : https://prove2.me/theorems/d66c42c4-37f2-416b-9e28-18bbe9895ffb
-- title:
--   S3x2: coe phi
-- statement:
--   The S3x2 construction uses the coe phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L242-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L242-L243

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

theorem Formalism.FourierDecayAlt.P.S3x2.coe_phi (h : GL (Fin k) A) :
    (phi A r k h : Matrix (Idx r k) (Idx r k) A) = hEmb r (h : Matrix (Fin k) (Fin k) A) := by sorry

attribute [defeq] Formalism.FourierDecayAlt.P.S3x2.coe_phi
