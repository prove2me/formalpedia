-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_two
-- name    : Formalism.FourierDecayAlt.P.FourTermExpansion.two
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:14:19.234992+00:00
-- url     : https://prove2.me/theorems/0fb5be76-be96-495a-810e-d042ebc2dfed
-- title:
--   Four Term Expansion: two
-- statement:
--   The Four Term Expansion construction uses the two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L209-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L209-L222

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

theorem Formalism.FourierDecayAlt.P.FourTermExpansion.two {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (x y : ℂ) (hxy : x - y = 1)
    (p q c d : Fin (2 * r + k + 1)) :
    Top (LT (Msg k r)) x p c (Top (LT (Msg k r)) y q d Φ) g
      - Top (LT (Msg k r)) x q c (Top (LT (Msg k r)) y p d Φ) g
      + Top (LT (Msg k r)) x p d (Top (LT (Msg k r)) y q c Φ) g
      - Top (LT (Msg k r)) x q d (Top (LT (Msg k r)) y p c Φ) g = 0 := by sorry
