-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LetterPairRecursion_step_pair
-- name    : Formalism.FourierDecayAlt.P.LetterPairRecursion.step_pair
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:26:07.946798+00:00
-- url     : https://prove2.me/theorems/dc3828a8-9ab0-4615-81bb-1f7310035b7b
-- title:
--   Letter Pair Recursion: step pair
-- statement:
--   The Letter Pair Recursion construction uses the step pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LetterPairStep.lean#L16-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LetterPairStep.lean#L16-L114

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LetterPairStep
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LetterPairRecursion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

theorem Formalism.FourierDecayAlt.P.LetterPairRecursion.step_pair (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hFm : CkOn (m : ℕ∞) (GV k r) F)
    (hDom1 : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS)
    (hDom2 : ∀ K : Set (Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p)
    (b : Bool) {X : Mat k r} (hX : unitLie k r X) {u v u2 v2 : List (Mat k r)}
    (hu : ∀ Y ∈ u, unitLie k r Y) (hv : ∀ Y ∈ v, unitLie k r Y) (hu2 : ∀ Y ∈ u2, unitLie k r Y)
    (hv2 : ∀ Y ∈ v2, unitLie k r Y) (hl2 : u2.length + v2.length ≤ m)
    (hl : u.length + v.length + 1 ≤ u2.length + v2.length)
    (hdl : ∀ f : Mat k r → (Wq →L[ℂ] Wp), dLR u2 v2 f = op b X (dLR u v f))
    (IH : ∀ g ∈ Om k r D.z D.z', dLR u v (JF D F) g = ∫ p, xiP D p • dLR u v (rho D p F) g ∂D.μSS) :
    ∀ g ∈ Om k r D.z D.z', dLR u2 v2 (JF D F) g = ∫ p, xiP D p • dLR u2 v2 (rho D p F) g ∂D.μSS := by sorry
