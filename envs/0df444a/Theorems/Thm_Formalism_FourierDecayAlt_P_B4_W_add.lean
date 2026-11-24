-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_add
-- name    : Formalism.FourierDecayAlt.P.B4.W_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:28.410065+00:00
-- url     : https://prove2.me/theorems/ac18823d-39ab-49eb-88e9-ccae0f2f4acf
-- title:
--   B4: W add
-- statement:
--   The B4 construction uses the W add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L486-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L486-L505

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

theorem Formalism.FourierDecayAlt.P.B4.W_add {f f₂ : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (hf : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f) (hf₂ : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂) :
    ∀ g ∈ GV k r, W w (f + f₂) g = W w f g + W w f₂ g := by sorry
