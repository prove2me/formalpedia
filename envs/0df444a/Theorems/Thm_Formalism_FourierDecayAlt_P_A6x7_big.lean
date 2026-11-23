-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_big
-- name    : Formalism.FourierDecayAlt.P.A6x7.big
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:29.89748+00:00
-- url     : https://prove2.me/theorems/8a065845-4230-4a19-93da-1608dd1ebc59
-- title:
--   A6x7: big
-- statement:
--   The A6x7 construction uses the big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L103-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L103-L120

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

theorem Formalism.FourierDecayAlt.P.A6x7.big (hD : LocalDatum K R ψ) {ϖ : Kˣ}
    (hϖ : (ϖ : K) ∈ R) (hϖ' : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (C : Set K)
    (hC : IsCompact C) : ∃ n : ℕ, ∀ y ∈ C, (ϖ : K) ^ n * y ∈ R := by sorry
