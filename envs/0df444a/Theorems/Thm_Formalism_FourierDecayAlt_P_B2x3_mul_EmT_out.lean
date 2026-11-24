-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_mul_EmT_out
-- name    : Formalism.FourierDecayAlt.P.B2x3.mul_EmT_out
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:43:53.561077+00:00
-- url     : https://prove2.me/theorems/c23762e9-42f7-4d43-a3b8-408e66cbb6fd
-- title:
--   B2x3: mul Em T out
-- statement:
--   The B2x3 construction uses the mul Em T out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L338-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L338-L345

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x3.mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : ¬ mid k r j) :
    (A * (Em k r)ᵀ) x j = 0 := by sorry
