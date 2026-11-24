-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_mid_add
-- name    : Formalism.FourierDecayAlt.P.B4.W_mid_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:27:29.806194+00:00
-- url     : https://prove2.me/theorems/c0f44824-fe41-4c3b-bf48-ad25f6fef3fa
-- title:
--   B4: W mid add
-- statement:
--   The B4 construction uses the W mid add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L736-L747
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L736-L747

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

theorem Formalism.FourierDecayAlt.P.B4.W_mid_add {F : Mat k r → E} (p q : List (Bool × Mat k r)) (b : Bool) {X Y : Mat k r}
    (hp : AllLie p) (hq : AllLie q) (hX : inLie k r X) (hY : inLie k r Y)
    (hF : CkOn ((p.length + 1 + q.length : ℕ) : ℕ∞) (GV k r) F) :
    ∀ g ∈ GV k r, W (p ++ (b, X + Y) :: q) F g = W (p ++ (b, X) :: q) F g + W (p ++ (b, Y) :: q) F g := by sorry
