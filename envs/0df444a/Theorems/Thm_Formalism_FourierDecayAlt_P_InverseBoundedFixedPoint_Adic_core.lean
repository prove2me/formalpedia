-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_core
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:58.243856+00:00
-- url     : https://prove2.me/theorems/75566d98-a62e-4197-b9e8-c2758790cb55
-- title:
--   Adic: core
-- statement:
--   The Adic construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L443-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L443-L500

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.core (h : Adic R ϖ) (𝔅 : Submodule R K) (hBR : ∀ x ∈ 𝔅, x ∈ R)
    (hBc : IsClosed (𝔅 : Set K)) (Y : (Fin m → K) → Matrix (Fin m) (Fin m) K)
    (hYR : ∀ v, (∀ k, v k ∈ 𝔅) → ∀ i j, Y v i j ∈ R)
    (hYL : ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      (∀ k, v k - v' k ∈ Λ) → MemM Λ (Y v - Y v')) :
    (∀ v, (∀ k, v k ∈ 𝔅) → ∀ k, (v + (ϖ : K) • (Y v *ᵥ v)) k ∈ 𝔅) ∧
    (∀ η : Fin m → K, (∀ k, η k ∈ 𝔅) → ∃ v, (∀ k, v k ∈ 𝔅) ∧ v + (ϖ : K) • (Y v *ᵥ v) = η) ∧
    ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ 𝔅) → (∀ k, v' k ∈ 𝔅) →
      ((∀ k, (v + (ϖ : K) • (Y v *ᵥ v)) k - (v' + (ϖ : K) • (Y v' *ᵥ v')) k ∈ Λ) ↔
        ∀ k, v k - v' k ∈ Λ) := by sorry
