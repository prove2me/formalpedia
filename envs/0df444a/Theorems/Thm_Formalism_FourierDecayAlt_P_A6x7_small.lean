-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_small
-- name    : Formalism.FourierDecayAlt.P.A6x7.small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:28.968314+00:00
-- url     : https://prove2.me/theorems/1f7414df-d899-4c39-a76d-31ba62c0a735
-- title:
--   A6x7: small
-- statement:
--   The A6x7 construction uses the small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L65-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L65-L101

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x7.small (hD : LocalDatum K R ψ) (h0 : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (V : Set K)
    (hV : V ∈ 𝓝 (0 : K)) : ∃ n : ℕ, ∀ r ∈ R, (ϖ : K) ^ n * r ∈ V := by sorry
