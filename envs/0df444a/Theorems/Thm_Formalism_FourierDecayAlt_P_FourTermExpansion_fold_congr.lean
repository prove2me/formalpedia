-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_congr
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.fold_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:15:09.298095+00:00
-- url     : https://prove2.me/theorems/831ebbf3-13bd-40ba-aa8b-3c0a36399337
-- title:
--   Four Term Expansion: fold congr
-- statement:
--   The Four Term Expansion construction uses the fold congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L83-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L83-L91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.fold_congr (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) {Φ₁ Φ₂ : Mat k r → E}
    {U : Set (Mat k r)} (hU : IsOpen U) (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) :
    ∀ x ∈ U, x ∈ GV k r → fold M ts Φ₁ x = fold M ts Φ₂ x := by sorry
