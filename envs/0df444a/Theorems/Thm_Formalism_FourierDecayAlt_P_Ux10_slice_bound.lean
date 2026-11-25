-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_slice_bound
-- name    : Formalism.FourierDecayAlt.P.Ux10.slice_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:24:12.127915+00:00
-- url     : https://prove2.me/theorems/8c134bcd-569d-4fdd-aee5-0159d2675ac4
-- title:
--   Ux10: slice bound
-- statement:
--   The Ux10 construction uses the slice bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L1245-L1307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L1245-L1307

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

theorem Formalism.FourierDecayAlt.P.Ux10.slice_bound (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) (hC : DerivativeCost) (hS : CoordinateDecay)
    {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (hs : 1 ≤ s)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Set.Ioi 0) (m mm Q : ℕ) (A₁ : ℝ) (hQ : m + 1 + mm ≤ Q)
    (ha : 0 < a1 (p + s + ρ) A₁ m mm) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F₁ : B.Mat k (p + s + ρ) → E) (B₁ : ℝ),
      Star k (p + s) ρ F₁ A₁ Q B₁ K → ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s), G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ,
      ∀ u v : List (B.Mat k ρ), unitW k ρ u → unitW k ρ v → u.length + v.length ≤ mm → ∀ q ≤ m + 1,
        ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) Z‖ ≤
          Cb * B₁ * ((1 + ‖Z‖) ^ (-a1 (p + s + ρ) A₁ m mm) * B.gN γ ^ (-a1 (p + s + ρ) A₁ m mm)) *
            wt ξ ^ (-a1 (p + s + ρ) A₁ m mm) := by sorry
