-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_comm
-- name    : Formalism.FourierDecayAlt.P.B4.op_comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:29:09.359799+00:00
-- url     : https://prove2.me/theorems/bf877f5c-2b53-439d-90cd-dc177c9e3353
-- title:
--   B4: op comm
-- statement:
--   The B4 construction uses the op comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L557-L569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L557-L569

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

theorem Formalism.FourierDecayAlt.P.B4.op_comm {f : Mat k r → E} {X Y g : Mat k r} (hf : CkOn ((2 : ℕ) : ℕ∞) (GV k r) f)
    (hX : inLie k r X) (hY : inLie k r Y) (hg : g ∈ GV k r) :
    op false Y (op true X f) g = op true X (op false Y f) g := by sorry
