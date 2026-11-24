-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_top
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:14:53.832855+00:00
-- url     : https://prove2.me/theorems/b9ff790c-4ff5-4165-ba0d-67febd68d189
-- title:
--   Four Term Expansion: EZ top
-- statement:
--   The Four Term Expansion construction uses the EZ top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L185-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L185-L200

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_top {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (Z : Mat k r)
    (y : ℂ) (q d : Fin (2 * r + k + 1)) :
    EZ Z (Top (LT (Msg k r)) y q d Φ) g =
      (if q = d then (1 : ℂ) else 0) • (y • EZ Z Φ g) + EZ Z (EZ (Msg k r q d) Φ) g := by sorry
