-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_rdV_congr
-- name    : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:29:21.216803+00:00
-- url     : https://prove2.me/theorems/648e19d0-3b97-4a4e-a86a-cdfded18c978
-- title:
--   Capelli Word Sum Expansion: rd V congr
-- statement:
--   The Capelli Word Sum Expansion construction uses the rd V congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliWordSumExpansion.lean#L70-L81

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr {f₁ f₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g X : Mat k r} (hg : g ∈ U)
    (hgG : g ∈ GV k r) (hX : inLie k r X) (he : ∀ x ∈ U, x ∈ GV k r → f₁ x = f₂ x) :
    RdV X f₁ g = RdV X f₂ g := by sorry
