-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_lin
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.fold_lin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:16:07.424796+00:00
-- url     : https://prove2.me/theorems/9fbf5562-fb64-46bc-9650-95d7187c66fa
-- title:
--   Four Term Expansion: fold lin
-- statement:
--   The Four Term Expansion construction uses the fold lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L120-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L120-L142

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.fold_lin (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (Φ₁ Φ₂ : Mat k r → E) (g : Mat k r), g ∈ GV k r → Loc (ts.length : ℕ∞) Φ₁ g →
      Loc (ts.length : ℕ∞) Φ₂ g → ∀ c : ℂ,
        fold M ts (fun x => Φ₁ x + c • Φ₂ x) g = fold M ts Φ₁ g + c • fold M ts Φ₂ g := by sorry
