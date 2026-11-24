-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_intRC
-- name    : Formalism.FourierDecayAlt.P.Ux6.intRC
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:29:02.187538+00:00
-- url     : https://prove2.me/theorems/78e11cdc-fef2-44da-a002-b72479e12bc8
-- title:
--   Ux6: int RC
-- statement:
--   The Ux6 construction uses the int RC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L509-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L509-L517

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6

theorem Formalism.FourierDecayAlt.P.Ux6.intRC (k j ρ : ℕ) (a : ℝ) (h : (((2 * ρ + k + 1) * (j * 2) + j * j * 2 + j : ℕ) : ℝ) < a) :
    Integrable (fun x : RC k j ρ => (1 + ‖x‖) ^ (-a)) (muRC k j ρ) := by sorry
