-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_fam_res
-- name    : Formalism.FourierDecayAlt.P.Qx3.fam_res
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:20:55.990337+00:00
-- url     : https://prove2.me/theorems/08ab09df-2a1d-4ef8-acbc-861d3a39b2c8
-- title:
--   Qx3: fam res
-- statement:
--   The Qx3 construction uses the fam res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L801-L816
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean#L801-L816

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
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P.Qx3.fam_res {j i : Fin (r + 1)} (hji : j ≤ i) {w : (Fin r → ℂ) → Mx k r} {ρ : (Fin r → ℂ) → ℂ}
    (hw : ContDiffOn ℝ ∞ w (OmX r)) (hρ : ContDiffOn ℝ ∞ ρ (OmX r))
    (hwG : ∀ c ∈ OmX r, w c ∈ Glev k r j) (hcomm : ∀ c ∈ OmX r, ∀ g ∈ Glev k r i, w c * g = g * w c)
    {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' j D) :
    FamFF k r z z' π π' i (fun c => {g | w c * g ∈ D}) (fun c g => ρ c • J (w c * g)) := by sorry
