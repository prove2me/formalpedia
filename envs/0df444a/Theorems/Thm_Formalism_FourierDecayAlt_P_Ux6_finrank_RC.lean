-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_RC
-- name    : Formalism.FourierDecayAlt.P.Ux6.finrank_RC
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:29:08.646616+00:00
-- url     : https://prove2.me/theorems/dbb786af-b267-406c-9b9f-74bdbe38b3fd
-- title:
--   Ux6: finrank RC
-- statement:
--   The Ux6 construction uses the finrank RC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L471-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L471-L476

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

theorem Formalism.FourierDecayAlt.P.Ux6.finrank_RC (k j ρ : ℕ) : Module.finrank ℝ (RC k j ρ) ≤ (2 * ρ + k + 1) * (j * 2) + j * j * 2 + j := by sorry
