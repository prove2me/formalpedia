-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_I
-- name    : Formalism.FourierDecayAlt.P.LieDecompositionLocal.EZ_I
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:14:55.652567+00:00
-- url     : https://prove2.me/theorems/0a1dc0a5-e644-493b-9474-11efefa7a706
-- title:
--   Lie Decomposition Local: EZ I
-- statement:
--   The Lie Decomposition Local construction uses the EZ I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L232-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L232-L246

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.LieDecompositionLocal.EZ_I {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r) (Z : Mat k r) :
    EZ (Complex.I • Z) Φ g = Complex.I • EZ Z Φ g := by sorry
