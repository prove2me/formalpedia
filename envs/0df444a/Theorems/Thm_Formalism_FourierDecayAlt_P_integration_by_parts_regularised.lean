-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_integration_by_parts_regularised
-- name    : Formalism.FourierDecayAlt.P.integration_by_parts_regularised
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:29:03.09938+00:00
-- url     : https://prove2.me/theorems/e0b957d1-d0b2-4b52-89a8-da79bddcfd72
-- title:
--   P: integration by parts regularised
-- statement:
--   The P construction uses the integration by parts regularised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralZeroFrequencyInvariant.lean#L376-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralZeroFrequencyInvariant.lean#L376-L376

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.integration_by_parts_regularised : Formalism.FourierDecayAlt.B.RegIBP := by sorry
