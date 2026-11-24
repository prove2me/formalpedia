-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HaarScaling_AB_le
-- name    : Formalism.FourierDecayAlt.P.HaarScaling.AB_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:57.853137+00:00
-- url     : https://prove2.me/theorems/0dbbc5e1-3447-48be-be9a-88272ee57d27
-- title:
--   Haar Scaling: AB le
-- statement:
--   The Haar Scaling construction uses the AB le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarScaling.lean#L31-L36

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaBOfComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarScaling
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.HaarScaling.AB_le (k r : ℕ) (A : ℝ) (h : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A) : AB k r ≤ A := by sorry
