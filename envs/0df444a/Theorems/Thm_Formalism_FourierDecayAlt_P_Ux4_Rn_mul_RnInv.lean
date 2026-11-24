-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_mul_RnInv
-- name    : Formalism.FourierDecayAlt.P.Ux4.Rn_mul_RnInv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:22:25.147374+00:00
-- url     : https://prove2.me/theorems/c1f9abf4-c668-483b-9f06-072996d7eb09
-- title:
--   Ux4: Rn mul Rn Inv
-- statement:
--   The Ux4 construction uses the Rn mul Rn Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L178-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L178-L183

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

theorem Formalism.FourierDecayAlt.P.Ux4.Rn_mul_RnInv (x : RC k j ρ) : Rn k j ρ x * RnInv x = 1 := by sorry
