-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_phi
-- name    : Formalism.FourierDecayAlt.P.S3x2.red_phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:39.374099+00:00
-- url     : https://prove2.me/theorems/75de85e0-0996-4f4a-a311-0bdc58cd8f79
-- title:
--   S3x2: red phi
-- statement:
--   The S3x2 construction uses the red phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L377-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L377-L380

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
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x2.red_phi (h : GL (Fin k) o) :
    red o (Idx r k) (phi o r k h) = phi 𝔽 r k (red o (Fin k) h) := by sorry
