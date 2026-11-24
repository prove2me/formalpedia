-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_herm_im_left
-- name    : Formalism.FourierDecayAlt.P.B2x5.measurable_herm_im_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:31.201351+00:00
-- url     : https://prove2.me/theorems/0a52278e-cecf-4a72-9c99-7f2391bc4691
-- title:
--   B2x5: measurable herm im left
-- statement:
--   The B2x5 construction uses the measurable herm im left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L650-L651
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L650-L651

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

theorem Formalism.FourierDecayAlt.P.B2x5.measurable_herm_im_left (k r : ℕ) (y₀ : Fin (2 * r + k + 1) → ℂ) :
    Measurable fun y : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) y y₀).im := by sorry
