-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_W_comm
-- name    : Formalism.FourierDecayAlt.P.B4.op_W_comm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:42.539648+00:00
-- url     : https://prove2.me/theorems/99abb293-2052-433c-8756-bc3f18fe1c49
-- title:
--   B4: op W comm
-- statement:
--   The B4 construction uses the op W comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L571-L587
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L571-L587

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

theorem Formalism.FourierDecayAlt.P.B4.op_W_comm {Z : Mat k r} (hZ : inLie k r Z) (u : List (Mat k r)) (hu : ∀ X ∈ u, inLie k r X) :
    ∀ K : Mat k r → E, CkOn ((u.length + 1 : ℕ) : ℕ∞) (GV k r) K → ∀ g ∈ GV k r,
      op false Z (W (lr u []) K) g = W (lr u []) (op false Z K) g := by sorry
