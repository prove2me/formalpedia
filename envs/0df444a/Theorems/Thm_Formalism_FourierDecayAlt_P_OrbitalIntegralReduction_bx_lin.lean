-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_lin
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:46.687406+00:00
-- url     : https://prove2.me/theorems/4e9c92f8-6111-4d74-9205-4d8d1dec4fc8
-- title:
--   Orbital Integral Reduction: bx lin
-- statement:
--   The Orbital Integral Reduction construction uses the bx lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L736-L798
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L736-L798

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
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_lin (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (hM : IsUnit M.det) (b : ι → K) {Λ L : AddSubgroup K} (hΛ : IsLat Λ) (hL : IsLat L)
    (f : (ι → K) → ℂ) (hinv : BInv Λ f) (hs : BSupp L f)
    (hR : ∀ ξ r : ι → K, (∀ i, r i ∈ R) → f (M *ᵥ (ξ + r) + b) = f (M *ᵥ ξ + b)) :
    bx R Λ ι f = (modK R M.det : ℂ) *
      ∑ᶠ q : ι → KR R, f (M *ᵥ (fun i => Quotient.out (q i)) + b) := by sorry
