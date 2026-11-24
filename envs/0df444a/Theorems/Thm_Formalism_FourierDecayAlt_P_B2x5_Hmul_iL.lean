-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_Hmul_iL
-- name    : Formalism.FourierDecayAlt.P.B2x5.Hmul_iL
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:56:38.8938+00:00
-- url     : https://prove2.me/theorems/4c4c0264-55ca-4d5b-a6d2-3bc042488261
-- title:
--   B2x5: Hmul i L
-- statement:
--   The B2x5 construction uses the Hmul i L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L184-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L184-L185

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

theorem Formalism.FourierDecayAlt.P.B2x5.Hmul_iL (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : (Hpk k (1 + r') *ᵥ u) (iL k r') = u (i0 k r') := by sorry
