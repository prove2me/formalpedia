-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_loc_add
-- name    : Formalism.FourierDecayAlt.P.LieDecompositionLocal.loc_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:47:58.127692+00:00
-- url     : https://prove2.me/theorems/cfb4abdb-9f01-44d8-b410-6f40423ab0c8
-- title:
--   Lie Decomposition Local: loc add
-- statement:
--   The Lie Decomposition Local construction uses the loc add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L138-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L138-L147

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

theorem Formalism.FourierDecayAlt.P.LieDecompositionLocal.loc_add {m : ℕ∞} {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m Φ₁ g) (h₂ : Loc m Φ₂ g) (c : ℂ) :
    Loc m (fun x => Φ₁ x + c • Φ₂ x) g := by sorry
