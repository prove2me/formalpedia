-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_le_div_of_lower_bound
-- name    : Formalism.FourierDecayAlt.P.Ux6.le_div_of_lower_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:34:45.357811+00:00
-- url     : https://prove2.me/theorems/adecea29-7962-4616-b7ab-3a4b5bb1f474
-- title:
--   Ux6: le div of lower bound
-- statement:
--   The Ux6 construction uses the le div of lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L286-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L286-L293

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

theorem Formalism.FourierDecayAlt.P.Ux6.le_div_of_lower_bound {X C y m m0 : ℝ} (hy : 0 ≤ y) (hm0 : 0 < m0) (hm : m0 ≤ m) (h : X ≤ C * y / m) :
    X ≤ max C 0 / m0 * y := by sorry
