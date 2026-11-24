-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_lin
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_lin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:04:45.319681+00:00
-- url     : https://prove2.me/theorems/df2c0568-8e84-47b9-b20e-bc89c186f401
-- title:
--   Four Term Expansion: EZ lin
-- statement:
--   The Four Term Expansion construction uses the EZ lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L30-L35

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_lin {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g) (hgG : g ∈ GV k r)
    (c : ℂ) (Z : Mat k r) : EZ Z (fun x => Φ₁ x + c • Φ₂ x) g = EZ Z Φ₁ g + c • EZ Z Φ₂ g := by sorry
