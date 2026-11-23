-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_point
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_point
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:54.600819+00:00
-- url     : https://prove2.me/theorems/3336b373-1b6f-4c71-8852-fca549062030
-- title:
--   Orbital Integral Reduction: pw point
-- statement:
--   The Orbital Integral Reduction construction uses the pw point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2577-L2637
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2577-L2637

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

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_point (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (hm : 1 ≤ m)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (t c D' : Kˣ)
    (htb : Sm R ϖ b (t : K)) (hDt : (D' : K) = (-1) ^ m * ((c : K) * (t : K) ^ m))
    (hQ : (D' : K) ∈ Q ∨ -(D' : K) ∈ Q)
    (hmain : ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p, y p ∈ L₀) → (HH (t : K) (Fin.cons ρ x : Fin (m + 1) → K) y).det = (D' : K) →
      Sm R ϖ b (ρ - x0 (D' : K) x) ∧
      ∃ r ∈ R, ρ * ((t⁻¹ : Kˣ) : K) = x0 (D' : K) x * ((t⁻¹ : Kˣ) : K) + g1 (D' : K) x y + r)
    (N : Pr (m + 1) → K) (hG : pw_Good R ϖ L₀ a ((t : K) • N)) (ξ : Fin m → K) :
    Φ (m + 1) ((Hm (t : K) (c : K) ξ (1 + EE N)).submatrix Fin.rev id) *
        ψ (lastE ξ + sUp (1 + EE N)) =
      ψ (g0 (D' : K) (xs ((t : K) • N)) * ((t⁻¹ : Kˣ) : K)) *
        ((modK R (∏ k, xs ((t : K) • N) k) : ℝ) : ℂ) *
        GG R ψ Φ (D' : K) (xs ((t : K) • N))
          (ys ((t : K) • N) (pw_Mx (t : K) (1 + EE N) *ᵥ ξ + pw_bv (c : K))) := by sorry
