-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_add
-- name    : Formalism.FourierDecayAlt.P.B4.op_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:29:26.331426+00:00
-- url     : https://prove2.me/theorems/02c491e0-b5a9-4326-9eee-45f316bf8ea0
-- title:
--   B4: op add
-- statement:
--   The B4 construction uses the op add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L360-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L360-L381

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.B4.op_add {f f₂ : Mat k r → E} {X g : Mat k r} (b : Bool) (hX : inLie k r X)
    (hf : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f) (hf₂ : CkOn ((1 : ℕ) : ℕ∞) (GV k r) f₂) (hg : g ∈ GV k r) :
    op b X (f + f₂) g = op b X f g + op b X f₂ g := by sorry
