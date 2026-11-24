-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_congr
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.top_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:39.538013+00:00
-- url     : https://prove2.me/theorems/db1baf0f-bca1-4179-9c85-562bcbe4f884
-- title:
--   Four Term Expansion: top congr
-- statement:
--   The Four Term Expansion construction uses the top congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L62-L66

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.top_congr {Φ₁ Φ₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U)
    (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    ∀ x ∈ U, x ∈ GV k r → Top (LT M) v a b Φ₁ x = Top (LT M) v a b Φ₂ x := by sorry
