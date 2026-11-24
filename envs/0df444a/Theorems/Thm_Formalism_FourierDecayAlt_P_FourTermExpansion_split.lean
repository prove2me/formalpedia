-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_split
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.split
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:29.610698+00:00
-- url     : https://prove2.me/theorems/ac172a2e-36c0-4112-bff0-238ce7864d63
-- title:
--   Four Term Expansion: split
-- statement:
--   The Four Term Expansion construction uses the split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L238-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L238-L249

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.split (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {t : ℕ}
    (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (i : ℕ) (hi : i + 1 < t) (Φ : Mat k r → E) :
    fold M (List.ofFn f) Φ = fold M ((List.ofFn f).take i)
      (Top (LT M) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
        (Top (LT M) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2
          (fold M ((List.ofFn f).drop (i + 2)) Φ))) := by sorry
