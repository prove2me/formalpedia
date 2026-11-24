-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_expandM
-- name    : Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.expandM
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:42:50.598243+00:00
-- url     : https://prove2.me/theorems/ab95a5fd-575b-47c0-8d20-aa17f50730c3
-- title:
--   Finite Sum Local Expansion: expand M
-- statement:
--   The Finite Sum Local Expansion construction uses the expand M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L140-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L140-L197

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.expandM (y : Mat k r) (hy : y ∈ GV k r) : ∀ (t : ℕ) (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (Φ : Mat k r → E) (x : Mat k r), x ∈ GV k r → Loc (t : ℕ∞) Φ x →
    fold (Mc y) (List.ofFn f) Φ x = ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
      (∏ j, ((y⁻¹) (c j) (f j).2.1 * y (f j).2.2 (d j))) •
        fold (Msg k r) (List.ofFn fun j => ((f j).1, c j, d j)) Φ x := by sorry
