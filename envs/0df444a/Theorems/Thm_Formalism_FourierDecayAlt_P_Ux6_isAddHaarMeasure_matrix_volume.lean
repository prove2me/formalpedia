-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_isAddHaarMeasure_matrix_volume
-- name    : Formalism.FourierDecayAlt.P.Ux6.isAddHaarMeasure_matrix_volume
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:23:05.126697+00:00
-- url     : https://prove2.me/theorems/9862dbaa-dba9-4968-aae4-3bac4d210cfb
-- title:
--   Ux6: is Add Haar Measure matrix volume
-- statement:
--   The Ux6 construction uses the is Add Haar Measure matrix volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L454-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L454-L455

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

theorem Formalism.FourierDecayAlt.P.Ux6.isAddHaarMeasure_matrix_volume (a b : ℕ) : (volume : Measure (Fin a → Fin b → ℂ)).IsAddHaarMeasure := by sorry
