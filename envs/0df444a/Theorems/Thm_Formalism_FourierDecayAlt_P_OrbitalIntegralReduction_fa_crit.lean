-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_crit
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_crit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:37.536882+00:00
-- url     : https://prove2.me/theorems/3ed3bd25-bfbc-4539-b79c-8e0b923aab10
-- title:
--   Orbital Integral Reduction: fa crit
-- statement:
--   The Orbital Integral Reduction construction uses the fa crit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2920-L3007
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2920-L3007

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

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_crit (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (hm : 1 ≤ m)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (D' z : Kˣ) (hz : z ^ (m + 1) = D') {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) :
    bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) (fun _ => (z : K))) =
      ((modK R (z : K) ^ (m * (m - 1) / 2) : ℝ) : ℂ) * omPhi R ψ (addBlock h0 (m + 1) z) Φ := by sorry
