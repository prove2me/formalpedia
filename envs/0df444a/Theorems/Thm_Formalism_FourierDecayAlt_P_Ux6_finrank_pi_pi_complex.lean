-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_finrank_pi_pi_complex
-- name    : Formalism.FourierDecayAlt.P.Ux6.finrank_pi_pi_complex
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:22:58.23209+00:00
-- url     : https://prove2.me/theorems/1ce725ea-ca96-4a00-ab12-af56ff9eeca4
-- title:
--   Ux6: finrank pi pi complex
-- statement:
--   The Ux6 construction uses the finrank pi pi complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L457-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L457-L458

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

theorem Formalism.FourierDecayAlt.P.Ux6.finrank_pi_pi_complex (a b : ℕ) : Module.finrank ℝ (Fin a → Fin b → ℂ) = a * (b * 2) := by sorry
