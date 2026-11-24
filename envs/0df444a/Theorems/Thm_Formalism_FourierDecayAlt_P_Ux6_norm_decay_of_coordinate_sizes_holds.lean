-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_norm_decay_of_coordinate_sizes_holds
-- name    : Formalism.FourierDecayAlt.P.Ux6.norm_decay_of_coordinate_sizes_holds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:35:14.573971+00:00
-- url     : https://prove2.me/theorems/1d5c9a7c-f72e-4a3d-981a-348ff4d186e4
-- title:
--   Ux6: norm decay of coordinate sizes holds
-- statement:
--   The Ux6 construction uses the norm decay of coordinate sizes holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L396-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L396-L450

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

theorem Formalism.FourierDecayAlt.P.Ux6.norm_decay_of_coordinate_sizes_holds : CoordinateDecayOfSizes := by sorry
