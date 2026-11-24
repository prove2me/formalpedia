-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_coef
-- name    : Formalism.FourierDecayAlt.P.B5.ckOn_coef
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:56:31.952805+00:00
-- url     : https://prove2.me/theorems/ef419e24-0d22-4357-af06-c83523a16bf5
-- title:
--   B5: ck On coef
-- statement:
--   The B5 construction uses the ck On coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L633-L654
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularisedPairingViaPhase.lean#L633-L654

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

theorem Formalism.FourierDecayAlt.P.B5.ckOn_coef {m : ℕ∞} {UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E)} {φ : Mat k r → E}
    (ha : CkOn ⊤ UU a) (hφ : CkOn m (GV k r) φ) (hs : closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ UU) :
    CkOn m (GV k r) (fun x => a x (φ x)) := by sorry
