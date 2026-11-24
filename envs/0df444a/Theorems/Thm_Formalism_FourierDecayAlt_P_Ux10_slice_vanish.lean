-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_slice_vanish
-- name    : Formalism.FourierDecayAlt.P.Ux10.slice_vanish
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:24:37.449213+00:00
-- url     : https://prove2.me/theorems/77dd113d-8342-4257-ada0-f561f1c904d4
-- title:
--   Ux10: slice vanish
-- statement:
--   The Ux10 construction uses the slice vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L1217-L1226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L1217-L1226

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.Ux10.slice_vanish (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F₁ : B.Mat k (p + s + ρ) → E} {A₁ B₁ : ℝ} {Q : ℕ} {K : Set ℝ} (hS : Star k (p + s) ρ F₁ A₁ Q B₁ K)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (hZ : G.detM Z ≠ 0) (hK : ‖(hMat σ d).det * G.detM Z‖ ∉ K) :
    ∀ γ ∈ B.GV k ρ, F₁ (gaXi k ρ σ d ξ Z γ) = 0 := by sorry
