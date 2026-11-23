-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_root_piece
-- name    : Formalism.FourierDecayAlt.P.HessianScalingIntegrals.root_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:52.756543+00:00
-- url     : https://prove2.me/theorems/a1bb7ec4-10f5-4d81-8bc6-fb8140ee9f01
-- title:
--   Hessian Scaling Integrals: root piece
-- statement:
--   The Hessian Scaling Integrals construction uses the root piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L147-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean#L147-L217

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
open Classical

theorem Formalism.FourierDecayAlt.P.HessianScalingIntegrals.root_piece [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
    (hγ : IsGamma R ψ m γ) (Λ₁ : AddSubgroup K) (B Λ : Submodule R K)
    (hB : IsLat B.toAddSubgroup) (hΛ : IsLat Λ.toAddSubgroup) (hΛB : Λ ≤ B)
    (hBΛ₁ : ∀ b ∈ B, b ∈ Λ₁)
    (A : (Fin m → K) → ℂ) (hA : LatInvN Λ₁ A) (t z : Kˣ) (D : K) (hD : (z : K) ^ (m + 1) = D)
    (hmod : 0 < modK R (z : K) ∧ 0 < modK R (t : K) ∧
      modK R ((z : K) * (t : K)) = modK R (z : K) * modK R (t : K))
    (hadm : GaussAdm ψ B.toAddSubgroup (hessM m (z * t)))
    (hmorse : ∃ φ : (Fin m → K) → (Fin m → K),
        Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
        (∀ Λ : Submodule R K, Λ ≤ B → ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
          ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
        ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
          (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
          g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
            ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ)))
    (hinv : LatInvN Λ.toAddSubgroup (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0)) :
    intK R Λ.toAddSubgroup m (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0) =
      ((modK R (t : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        (γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K))) := by sorry
