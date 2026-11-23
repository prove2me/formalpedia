-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_inv_bdd
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.inv_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:16.681055+00:00
-- url     : https://prove2.me/theorems/d3786aea-a4de-4184-b19f-c2c8b637d929
-- title:
--   Kernel Scaling Back: inv bdd
-- statement:
--   The Kernel Scaling Back construction uses the inv bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L501-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L501-L536

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.inv_bdd [TopologicalSpace K] [IsTopologicalRing K] (ho : IsOpen (R : Set K)) (ϖ : Kˣ)
    (hϖ : (ϖ : K) ∈ R) (hu : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (Om : Set K)
    (hOm : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ N : ℕ, ∀ z : Kˣ, (z : K) ∈ Om → (ϖ : K) ^ N * ((z⁻¹ : Kˣ) : K) ∈ R := by sorry
