-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_coordinate_sizes_of_parts
-- name    : Formalism.FourierDecayAlt.P.coordinate_sizes_of_parts
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:58:17.079136+00:00
-- url     : https://prove2.me/theorems/b3e1cd03-c9ea-4940-9da2-4aa0ea53b5cf
-- title:
--   P: coordinate sizes of parts
-- statement:
--   The P construction uses the coordinate sizes of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L549-L549
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L549-L549

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

theorem Formalism.FourierDecayAlt.P.coordinate_sizes_of_parts : Formalism.FourierDecayAlt.U.CoordinateSizesFromComponents := by sorry
