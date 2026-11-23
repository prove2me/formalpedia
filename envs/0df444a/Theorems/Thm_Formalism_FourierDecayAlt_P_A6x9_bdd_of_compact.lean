-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x9_bdd_of_compact
-- name    : Formalism.FourierDecayAlt.P.A6x9.bdd_of_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:23.113116+00:00
-- url     : https://prove2.me/theorems/54acbc96-9013-4cc3-9337-f24ed52db8d1
-- title:
--   A6x9: bdd of compact
-- statement:
--   The A6x9 construction uses the bdd of compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L290-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PadicChangeOfVariables.lean#L290-L296

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)

theorem Formalism.FourierDecayAlt.P.A6x9.bdd_of_compact (hd : LocalDatum K R ψ) (hπ : (π : K) ∈ R)
    (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ R) {C : Set K} (hC : IsCompact C) :
    ∃ k : ℕ, ∀ z ∈ C, (π : K) ^ k * z ∈ R := by sorry
