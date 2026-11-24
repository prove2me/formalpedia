-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOnGoodSet_good_set
-- name    : Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.good_set
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:05:55.699673+00:00
-- url     : https://prove2.me/theorems/e08f9abc-8a1f-4145-922d-7e51f4c622de
-- title:
--   Smoothness On Good Set: good set
-- statement:
--   The Smoothness On Good Set construction uses the good set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothnessOnGoodSet.lean#L120-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothnessOnGoodSet.lean#L120-L148

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.good_set (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F)
    {K : Set (Mat k r)} (hK : IsCompact K) (hKG : K ⊆ GV k r)
    {WS : Set (List (Mat k r) × List (Mat k r))} (hWS : WS.Countable)
    (hWSl : ∀ uv ∈ WS, (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m)
    (b : SS k r → ℝ)
    (hb : ∀ uv ∈ WS, ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖rho D p (dLR (uv.1.map (AdL p)) (uv.2.map (AdR p)) F) g‖ ≤ b p) :
    ∀ᵐ p ∂D.μSS, D.inSS p ∧ ∀ uv ∈ WS, ∀ g ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g‖ ≤ b p := by sorry
