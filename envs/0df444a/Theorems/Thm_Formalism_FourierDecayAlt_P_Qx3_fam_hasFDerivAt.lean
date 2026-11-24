-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_fam_hasFDerivAt
-- name    : Formalism.FourierDecayAlt.P.Qx3.fam_hasFDerivAt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:31.953656+00:00
-- url     : https://prove2.me/theorems/4360efee-7581-4db2-a53d-76796f2a05f2
-- title:
--   Qx3: fam has FDeriv At
-- statement:
--   The Qx3 construction uses the fam has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L394-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L394-L410

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}

theorem Formalism.FourierDecayAlt.P.Qx3.fam_hasFDerivAt {Φ : Fn k r E} {U : Set (XX k r)} {F : XX k r → E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x) {x : XX k r} (hx : x ∈ U)
    (hxG : x.2 ∈ Glev k r i) :
    HasFDerivAt (fun c' => Φ c' x.2)
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ (Fin r → ℂ) (Mx k r))) x.1 := by sorry
