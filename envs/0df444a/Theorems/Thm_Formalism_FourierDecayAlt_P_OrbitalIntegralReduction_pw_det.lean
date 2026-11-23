-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_det
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:42.807534+00:00
-- url     : https://prove2.me/theorems/16695d4f-7b01-4338-820f-4772f7cdceaf
-- title:
--   Orbital Integral Reduction: pw det
-- statement:
--   The Orbital Integral Reduction construction uses the pw det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2235-L2273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2235-L2273

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

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_det (hC : Cst R ϖ L₀ Λ₀ Q a b) (m : ℕ) :
    ∃ M₃ : ℕ, ∀ t : K, Sm R ϖ M₃ t → ∀ (ρ : K) (x : Fin m → K) (y : Pr (m + 1) → K),
      (∀ k, x k ∈ L₀ ∧ IsUnit (x k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (x k))) →
      (∀ p : Pr (m + 1), p.1.1 ≠ 0 → y p ∈ L₀) →
      IsUnit ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det ∧
      modK R ((HH t (Fin.cons ρ x : Fin (m + 1) → K) y).submatrix Fin.succ Fin.succ).det =
        modK R (∏ k, x k) := by sorry
