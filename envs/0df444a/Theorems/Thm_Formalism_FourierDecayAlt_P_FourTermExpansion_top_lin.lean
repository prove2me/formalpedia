-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_lin
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.top_lin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:06:15.067594+00:00
-- url     : https://prove2.me/theorems/c5251b25-50a2-4ca4-a022-e8e3dcb45754
-- title:
--   Four Term Expansion: top lin
-- statement:
--   The Four Term Expansion construction uses the top lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L68-L72

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.top_lin {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g) (hgG : g ∈ GV k r)
    (c : ℂ) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (LT M) v a b (fun x => Φ₁ x + c • Φ₂ x) g = Top (LT M) v a b Φ₁ g + c • Top (LT M) v a b Φ₂ g := by sorry
