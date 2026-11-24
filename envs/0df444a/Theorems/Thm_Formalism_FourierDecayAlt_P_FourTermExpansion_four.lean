-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_four
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.four
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:13:58.708625+00:00
-- url     : https://prove2.me/theorems/f6a2f794-f12c-46c4-ab0a-56c36187e0d8
-- title:
--   Four Term Expansion: four
-- statement:
--   The Four Term Expansion construction uses the four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L251-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L251-L315

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.four {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (i : ℕ)
    (hi : i + 1 < t)
    (h₂ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₂ j = f₁ j)
    (h₃ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₃ j = f₁ j)
    (h₄ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₄ j = f₁ j)
    (hmid : ∀ (Ψ : Mat k r → E) (x : Mat k r), x ∈ GV k r → Loc 2 Ψ x →
      (let P := fun (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) =>
        Top (LT (Msg k r)) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
          (Top (LT (Msg k r)) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2 Ψ) x
       P f₁ - P f₂ + P f₃ - P f₄ = 0))
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) :
    fold (Msg k r) (List.ofFn f₁) Φ g - fold (Msg k r) (List.ofFn f₂) Φ g +
      fold (Msg k r) (List.ofFn f₃) Φ g - fold (Msg k r) (List.ofFn f₄) Φ g = 0 := by sorry
