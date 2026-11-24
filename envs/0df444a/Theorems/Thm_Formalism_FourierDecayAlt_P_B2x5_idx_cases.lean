-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_idx_cases
-- name    : Formalism.FourierDecayAlt.P.B2x5.idx_cases
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:27.219007+00:00
-- url     : https://prove2.me/theorems/9f483cee-614f-4e20-a83f-46f9579c41fa
-- title:
--   B2x5: idx cases
-- statement:
--   The B2x5 construction uses the idx cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L113-L123

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

theorem Formalism.FourierDecayAlt.P.B2x5.idx_cases (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    p = i0 k r' ∨ (∃ j, p = levPos k 1 r' j) ∨ p = iL k r' := by sorry
