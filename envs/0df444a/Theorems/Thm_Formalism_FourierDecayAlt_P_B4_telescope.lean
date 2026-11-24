-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_telescope
-- name    : Formalism.FourierDecayAlt.P.B4.telescope
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:30:56.267849+00:00
-- url     : https://prove2.me/theorems/f038bf9a-9532-46c9-9ae3-ada993c95441
-- title:
--   B4: telescope
-- statement:
--   The B4 construction uses the telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L752-L834
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L752-L834

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

theorem Formalism.FourierDecayAlt.P.B4.telescope {F : Mat k r → E} {A c K ε : ℝ} {m : ℕ} (h : CCle A m F c) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (φ : Bool × Mat k r → Bool × Mat k r) (hφ1 : ∀ x, (φ x).1 = x.1)
    (hφL : ∀ x, unitLie k r x.2 → inLie k r (φ x).2)
    (hφK : ∀ x, unitLie k r x.2 → ‖(φ x).2‖ ≤ K)
    (hφε : ∀ x, unitLie k r x.2 → ‖(φ x).2 - x.2‖ ≤ ε) :
    ∀ (w p : List (Bool × Mat k r)), (∀ x ∈ p, unitLie k r x.2) → (∀ x ∈ w, unitLie k r x.2) →
      LRt ((p ++ w).map Prod.fst) → (p ++ w).length ≤ m → ∀ g ∈ GV k r,
      gN g ^ A * ‖W (p ++ w.map φ) F g - W (p ++ w) F g‖ ≤ w.length * (K ^ m * ε * c) := by sorry
