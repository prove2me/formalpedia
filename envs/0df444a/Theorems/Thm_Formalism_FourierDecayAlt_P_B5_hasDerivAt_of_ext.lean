-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hasDerivAt_of_ext
-- name    : Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:53:20.096703+00:00
-- url     : https://prove2.me/theorems/51af55da-36fe-4c65-a1bd-b5273b1ca02a
-- title:
--   B5: has Deriv At of ext
-- statement:
--   The B5 construction uses the has Deriv At of ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L541-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L541-L557

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.B5.hasDerivAt_of_ext {f f' : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g X : Mat k r}
    (hg : g ∈ U) (hgG : g ∈ GV k r) (hX : inLie k r X) (hf' : DifferentiableAt ℝ f' g)
    (he : ∀ x ∈ U, x ∈ GV k r → f x = f' x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ f' g (g * X)) 0 := by sorry
