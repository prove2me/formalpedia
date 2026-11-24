-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_split
-- name    : Formalism.FourierDecayAlt.P.B2x5.herm_split
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:00:42.99759+00:00
-- url     : https://prove2.me/theorems/c96d0ef0-c9ff-4ca3-ac3d-435ee179098e
-- title:
--   B2x5: herm split
-- statement:
--   The B2x5 construction uses the herm split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L194-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L194-L202

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

theorem Formalism.FourierDecayAlt.P.B2x5.herm_split (k r' : ℕ) (u v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u v =
      conj (v (i0 k r')) * u (iL k r') + herm (Hpk k r') (res k r' u) (res k r' v) + conj (v (iL k r')) * u (i0 k r') := by sorry
