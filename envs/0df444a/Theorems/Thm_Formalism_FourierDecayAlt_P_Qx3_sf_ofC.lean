-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_ofC
-- name    : Formalism.FourierDecayAlt.P.Qx3.sf_ofC
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:10:32.20168+00:00
-- url     : https://prove2.me/theorems/c5554fe6-c334-47a3-867e-1eef19ecd8e5
-- title:
--   Qx3: sf of C
-- statement:
--   The Qx3 construction uses the sf of C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L389-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L389-L392

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

theorem Formalism.FourierDecayAlt.P.Qx3.sf_ofC {ρ : (Fin r → ℂ) → ℂ} (hρ : ContDiffOn ℝ ∞ ρ (OmX r)) (hU₀ : U₀ ⊆ {x | x.1 ∈ OmX r}) :
    SmoothFam k r i U₀ (fun c _ => ρ c) := by sorry
