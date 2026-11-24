-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dil_bound1
-- name    : Formalism.FourierDecayAlt.P.B4.dil_bound1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:31:28.914363+00:00
-- url     : https://prove2.me/theorems/0dc5d6dd-3e2e-45cb-989f-982fa7395490
-- title:
--   B4: dil bound1
-- statement:
--   The B4 construction uses the dil bound1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1362-L1402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L1362-L1402

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2

theorem Formalism.FourierDecayAlt.P.B4.dil_bound1 {F : Mat k r → E} {A c : ℝ} {m : ℕ} (hA : 0 ≤ A) (hF : CCle A m F c) :
    CCle A m (dl t F) (((4 : ℝ) ^ r) ^ A * ((4 ^ r) ^ m * c)) := by sorry
