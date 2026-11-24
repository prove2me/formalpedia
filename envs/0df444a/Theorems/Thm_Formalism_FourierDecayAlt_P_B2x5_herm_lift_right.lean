-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_lift_right
-- name    : Formalism.FourierDecayAlt.P.B2x5.herm_lift_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:48.518375+00:00
-- url     : https://prove2.me/theorems/a736e937-1486-4b39-a6f9-d6c1dd60c48e
-- title:
--   B2x5: herm lift right
-- statement:
--   The B2x5 construction uses the herm lift right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L299-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L299-L302

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x5.herm_lift_right (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (liftVec k 1 r' y) = herm (Hpk k r') (res k r' u) y := by sorry
