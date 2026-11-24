-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_herm_im_right
-- name    : Formalism.FourierDecayAlt.P.B2x5.measurable_herm_im_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:58:29.808961+00:00
-- url     : https://prove2.me/theorems/726f7c0d-84db-47cc-9403-d20a30bc41e8
-- title:
--   B2x5: measurable herm im right
-- statement:
--   The B2x5 construction uses the measurable herm im right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L653-L654
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L653-L654

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

theorem Formalism.FourierDecayAlt.P.B2x5.measurable_herm_im_right (k r : ℕ) (y₀ : Fin (2 * r + k + 1) → ℂ) :
    Measurable fun y : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) y₀ y).im := by sorry
