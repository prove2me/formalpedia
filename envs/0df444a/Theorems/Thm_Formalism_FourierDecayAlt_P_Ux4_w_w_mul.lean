-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_w_w_mul
-- name    : Formalism.FourierDecayAlt.P.Ux4.w_w_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:54:49.330968+00:00
-- url     : https://prove2.me/theorems/07da9923-a230-4bec-8486-0b774adaf185
-- title:
--   Ux4: w w mul
-- statement:
--   The Ux4 construction uses the w w mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L166-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L166-L167

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

theorem Formalism.FourierDecayAlt.P.Ux4.w_w_mul (M : Matrix (Fin j) (Fin j) ℂ) : G.wMat j * (G.wMat j * M) = M := by sorry
