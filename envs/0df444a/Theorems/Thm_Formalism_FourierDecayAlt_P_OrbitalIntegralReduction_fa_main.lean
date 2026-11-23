-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_main
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:39.561778+00:00
-- url     : https://prove2.me/theorems/798c842a-5453-45ee-a0dc-ab26501b05b2
-- title:
--   Orbital Integral Reduction: fa main
-- statement:
--   The Orbital Integral Reduction construction uses the fa main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L3029-L3221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L3029-L3221

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_main (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) (hL₀ : IsLat L₀) {m : ℕ}
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c D' : Kˣ) (hD'Q : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q) {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) (htR : (t : K) ∈ R)
    (hLA : ∀ N : Pr (m + 1) → K,
      ∑ᶠ ξ : Fin m → KR R,
        Φ (m + 1) ((Hm (t : K) (c : K) (outV R ξ) (1 + EE N)).submatrix Fin.rev id) *
          ψ (lastE (outV R ξ) + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Fin m)
          (fun τ => GG R ψ Φ (D' : K) (xs ((t : K) • N)) (ys ((t : K) • N) τ)))
    (Λ : AddSubgroup K) (hΛ : IsLat Λ)
    (hΛinv : LatInvN Λ (fun x : Fin m → K =>
      bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
        ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K)))) :
    omPhi R ψ (pt2 h0 m t c) Φ = ((((modK R (t : K)) ^ (m * (m + 1) / 2))⁻¹ : ℝ) : ℂ) *
      intK R Λ m (fun x : Fin m → K =>
        bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) x) *
          ψ (g0 (D' : K) x * ((t⁻¹ : Kˣ) : K))) := by sorry
