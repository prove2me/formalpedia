-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_integrability_top_level
-- name    : Formalism.FourierDecayAlt.P.integrability_top_level
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:38:13.335844+00:00
-- url     : https://prove2.me/theorems/3f4025d1-c26c-46dd-9c14-e8ee06bad8e1
-- title:
--   P: integrability top level
-- statement:
--   The P construction uses the integrability top level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L555-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L555-L555

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

theorem Formalism.FourierDecayAlt.P.integrability_top_level : Formalism.FourierDecayAlt.U.IntTop := by sorry
