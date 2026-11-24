-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_ckOn_W_top
-- name    : Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_W_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:30:17.604567+00:00
-- url     : https://prove2.me/theorems/fa87734a-34a5-477d-9ad8-67c9f3343122
-- title:
--   Smoothness Order Arithmetic: ck On W top
-- statement:
--   The Smoothness Order Arithmetic construction uses the ck On W top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L54-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L54-L60

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_W_top {f : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (hf : CkOn (⊤ : ℕ∞) (GV k r) f) : CkOn (⊤ : ℕ∞) (GV k r) (W w f) := by sorry
