-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisG_mul
-- name    : Formalism.FourierDecayAlt.P.B2x5.heisG_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:56:33.746641+00:00
-- url     : https://prove2.me/theorems/212201f8-506f-4a69-a7ca-6a32640c0b9c
-- title:
--   B2x5: heis G mul
-- statement:
--   The B2x5 construction uses the heis G mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L326-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L326-L341

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

theorem Formalism.FourierDecayAlt.P.B2x5.heisG_mul (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) (b b' : ℂ) :
    heisG k r' (liftVec k 1 r' y) b * heisG k r' (liftVec k 1 r' y') b' =
      heisG k r' (liftVec k 1 r' (y + y')) (b + b' - herm (Hpk k r') y' y) := by sorry
