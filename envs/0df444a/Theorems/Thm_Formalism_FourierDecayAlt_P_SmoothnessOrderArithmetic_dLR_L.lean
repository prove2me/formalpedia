-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_dLR_L
-- name    : Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.dLR_L
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:33.409047+00:00
-- url     : https://prove2.me/theorems/3028ce6c-372a-4090-9cfc-e8f505d562c2
-- title:
--   Smoothness Order Arithmetic: d LR L
-- statement:
--   The Smoothness Order Arithmetic construction uses the d LR L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L96-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L96-L105

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

theorem Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.dLR_L {u v : List (Mat k r)} {X : Mat k r} (hu : ∀ Y ∈ u, inLie k r Y) (hv : ∀ Y ∈ v, inLie k r Y)
    (hX : inLie k r X) {F : Mat k r → E} (hF : CkOn (⊤ : ℕ∞) (GV k r) F) :
    ∀ g ∈ GV k r, dLR u v (LdV X F) g = dLR (u ++ [X]) v F g := by sorry
