-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_cons
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.fold_cons
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:05:09.123617+00:00
-- url     : https://prove2.me/theorems/f1874048-3b43-4aed-be61-2fe72429ec3c
-- title:
--   Four Term Expansion: fold cons
-- statement:
--   The Four Term Expansion construction uses the fold cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L52-L53

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.fold_cons (t : ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (ts) (Φ : Mat k r → E) :
    fold M (t :: ts) Φ = Top (LT M) t.1 t.2.1 t.2.2 (fold M ts Φ) := by sorry
