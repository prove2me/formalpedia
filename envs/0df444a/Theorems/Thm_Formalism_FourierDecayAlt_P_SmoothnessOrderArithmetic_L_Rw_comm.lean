-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_L_Rw_comm
-- name    : Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.L_Rw_comm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:31.054853+00:00
-- url     : https://prove2.me/theorems/45229f34-1955-4944-a0d9-88aaf8333937
-- title:
--   Smoothness Order Arithmetic: L Rw comm
-- statement:
--   The Smoothness Order Arithmetic construction uses the L Rw comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L76-L90

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

theorem Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.L_Rw_comm {X : Mat k r} (hX : inLie k r X) : ∀ (v : List (Mat k r)), (∀ Y ∈ v, inLie k r Y) →
    ∀ K : Mat k r → E, CkOn (⊤ : ℕ∞) (GV k r) K → ∀ g ∈ GV k r,
      Rw v (LdV X K) g = LdV X (Rw v K) g := by sorry
