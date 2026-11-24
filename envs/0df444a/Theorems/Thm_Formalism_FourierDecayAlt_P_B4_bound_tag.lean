-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_tag
-- name    : Formalism.FourierDecayAlt.P.B4.bound_tag
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:30:49.678998+00:00
-- url     : https://prove2.me/theorems/4c729fcc-2af7-488e-9d6c-04eed218afc1
-- title:
--   B4: bound tag
-- statement:
--   The B4 construction uses the bound tag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L639-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L639-L652

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

theorem Formalism.FourierDecayAlt.P.B4.bound_tag {F : Mat k r → E} {A c : ℝ} {m : ℕ} (h : CCle A m F c) (w : List (Bool × Mat k r))
    (ht : LRt (w.map Prod.fst)) (hu : ∀ x ∈ w, unitLie k r x.2) (hl : w.length ≤ m) :
    ∀ g ∈ GV k r, gN g ^ A * ‖W w F g‖ ≤ c := by sorry
