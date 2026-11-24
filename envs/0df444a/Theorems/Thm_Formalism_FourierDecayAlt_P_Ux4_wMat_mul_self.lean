-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_wMat_mul_self
-- name    : Formalism.FourierDecayAlt.P.Ux4.wMat_mul_self
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:47:29.662083+00:00
-- url     : https://prove2.me/theorems/12ec3289-1b46-4f50-968d-3126084a4c76
-- title:
--   Ux4: w Mat mul self
-- statement:
--   The Ux4 construction uses the w Mat mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L109-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L109-L121

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux4.wMat_mul_self (d : ℕ) : G.wMat d * G.wMat d = 1 := by sorry
