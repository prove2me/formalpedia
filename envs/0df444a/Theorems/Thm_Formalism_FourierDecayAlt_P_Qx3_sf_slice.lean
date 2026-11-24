-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_slice
-- name    : Formalism.FourierDecayAlt.P.Qx3.sf_slice
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:23.901679+00:00
-- url     : https://prove2.me/theorems/78fdce37-2647-42e3-ba0d-a68c4531b54b
-- title:
--   Qx3: sf slice
-- statement:
--   The Qx3 construction uses the sf slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L490-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L490-L497

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

theorem Formalism.FourierDecayAlt.P.Qx3.sf_slice {Dc : (Fin r → ℂ) → Set (Mx k r)} {Φ : Fn k r E}
    (h : SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Φ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    SmoothLev k r i (Dc c) (Φ c) := by sorry
