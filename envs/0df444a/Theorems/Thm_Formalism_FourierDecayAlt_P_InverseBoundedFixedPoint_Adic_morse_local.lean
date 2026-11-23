-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_morse_local
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.morse_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:05.327472+00:00
-- url     : https://prove2.me/theorems/f4d3ff9d-04ee-4445-a833-caa467117deb
-- title:
--   Adic: morse local
-- statement:
--   The Adic construction uses the morse local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L745-L940
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L745-L940

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
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.morse_local (h : Adic R ϖ) (h2 : IsUnit (2 : K)) (m : ℕ) (c z : Kˣ)
    (hcv : (c : K) = 4 * ((m + 1 : ℕ) : K) * (ϖ : K)) (B : Submodule R K)
    (hBc : IsClosed (B : Set K)) (hBz : ∀ b ∈ B, ∃ r ∈ R, b = (z : K) * (c : K) * r) :
    ∃ φ : (Fin m → K) → (Fin m → K),
      Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
      (∀ Λ : Submodule R K, ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
        ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
      ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
        (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
        g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
          ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ)) := by sorry
