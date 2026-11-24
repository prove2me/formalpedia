-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_last_ne_first_index
-- name    : Formalism.FourierDecayAlt.P.B2x5.last_ne_first_index
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:58.627976+00:00
-- url     : https://prove2.me/theorems/cf27f31c-149f-49e4-8f57-6fd3902f3813
-- title:
--   B2x5: last ne first index
-- statement:
--   The B2x5 construction uses the last ne first index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L204-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L204-L208

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

theorem Formalism.FourierDecayAlt.P.B2x5.last_ne_first_index (k r' : ℕ) : iL k r' ≠ i0 k r' := by sorry
