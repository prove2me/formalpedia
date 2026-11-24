-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_op_ext
-- name    : Formalism.FourierDecayAlt.P.B4.op_op_ext
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:27:01.683388+00:00
-- url     : https://prove2.me/theorems/b861c037-5279-44cb-9224-0ba0439ced3f
-- title:
--   B4: op op ext
-- statement:
--   The B4 construction uses the op op ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L542-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L542-L555

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

theorem Formalism.FourierDecayAlt.P.B4.op_op_ext {f f' : Mat k r → E} {U : Set (Mat k r)} {X Y g : Mat k r} (b b' : Bool)
    (hU : IsOpen U) (hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U)
    (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h) (hX : inLie k r X) (hY : inLie k r Y)
    (hg : g ∈ U) (hgG : g ∈ GV k r) :
    op b X (op b' Y f) g =
      fderiv ℝ (fderiv ℝ f') g (vf b X g) (vf b' Y g) + fderiv ℝ f' g (vf b' Y (vf b X g)) := by sorry
