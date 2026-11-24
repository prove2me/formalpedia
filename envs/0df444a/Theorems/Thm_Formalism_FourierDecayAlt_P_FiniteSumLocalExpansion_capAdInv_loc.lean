-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_capAdInv_loc
-- name    : Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv_loc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:51.07525+00:00
-- url     : https://prove2.me/theorems/8053a415-4e96-4ec8-9e9e-883ae606cb11
-- title:
--   Finite Sum Local Expansion: cap Ad Inv loc
-- statement:
--   The Finite Sum Local Expansion construction uses the cap Ad Inv loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L324-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L324-L388

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

theorem Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.capAdInv_loc (y : Mat k r) (hy : y ∈ GV k r) (u : ℂ) (f : Mat k r → E) (h : Mat k r) (hh : h ∈ GV k r)
    (hloc : Loc ((Q.mdim k r 0 : ℕ) : ℕ∞) f h) :
    qminorOp (Formalism.FourierDecayAlt.P.JFxB.EHc k r y) (Q.posL k r 0) (Q.posL k r 0) u f h =
      qminorOp (Q.EH k r) (Q.posL k r 0) (Q.posL k r 0) u f h := by sorry
