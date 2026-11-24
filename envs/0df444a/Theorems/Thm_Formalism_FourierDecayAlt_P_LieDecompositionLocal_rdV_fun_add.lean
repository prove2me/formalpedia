-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_fun_add
-- name    : Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:48:44.710236+00:00
-- url     : https://prove2.me/theorems/f8602ba1-d762-46e9-818d-9bd7ebfd9132
-- title:
--   Lie Decomposition Local: rd V fun add
-- statement:
--   The Lie Decomposition Local construction uses the rd V fun add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L126-L129

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

theorem Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add {Φ₁ Φ₂ : Mat k r → E} {g X : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g)
    (hgG : g ∈ GV k r) (hX : inLie k r X) (c : ℂ) :
    RdV X (fun x => Φ₁ x + c • Φ₂ x) g = RdV X Φ₁ g + c • RdV X Φ₂ g := by sorry
