-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B5_word_adj
-- name    : Formalism.FourierDecayAlt.P.B5.word_adj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:56:31.3588+00:00
-- url     : https://prove2.me/theorems/bb09dfce-58f5-4c55-ba9c-09ae5d0c3984
-- title:
--   B5: word adj
-- statement:
--   The B5 construction uses the word adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L732-L779
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L732-L779

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.B5.word_adj (D : RealPlaceData k r Wp Wq) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) {N : ℕ}
    (hN : w.length + 1 ≤ N) {f φ : Mat k r → (Wq →L[ℂ] Wp)} (hf : CkOn (N : ℕ∞) (GV k r) f)
    (hφ : CkOn (N : ℕ∞) (GV k r) φ)
    (hI : ∀ i j : ℕ, i ≤ j → j ≤ w.length → Integrable (fun g : Mt k r =>
      ‖Rw (w.take i).reverse φ (Matrix.of g)‖ * ‖Rw (w.drop j) f (Matrix.of g)‖) D.μG)
    (j : ℕ) (hj : j ≤ w.length) :
    (∫ g : Mt k r, hsInner (Rw w f (Matrix.of g)) (φ (Matrix.of g)) ∂D.μG) =
      (-1) ^ j * ∫ g : Mt k r, hsInner (Rw (w.drop j) f (Matrix.of g))
        (Rw (w.take j).reverse φ (Matrix.of g)) ∂D.μG := by sorry
