-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_smul_fun
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_smul_fun
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:47.227072+00:00
-- url     : https://prove2.me/theorems/62bd2294-5a30-47a0-b01e-c5e4df97146d
-- title:
--   Four Term Expansion: EZ smul fun
-- statement:
--   The Four Term Expansion construction uses the EZ smul fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L174-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L174-L183

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_smul_fun {Φ : Mat k r → E} {g : Mat k r} (h : Loc 1 Φ g) (hgG : g ∈ GV k r) (c : ℂ)
    (Z : Mat k r) : EZ Z (fun x => c • Φ x) g = c • EZ Z Φ g := by sorry
