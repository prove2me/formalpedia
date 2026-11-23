-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_inv_mem_of_near
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.inv_mem_of_near
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:52.319177+00:00
-- url     : https://prove2.me/theorems/88f04442-c2ff-4800-b0e0-6f118ebf02e3
-- title:
--   Kernel Scaling Back: inv mem of near
-- statement:
--   The Kernel Scaling Back construction uses the inv mem of near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L480-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L480-L499

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

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.inv_mem_of_near (ϖ : K) (hϖ : ϖ ∈ R) (hu : ∀ x : K, ∃ m : ℕ, ϖ ^ m * x ∈ R) (x : Kˣ)
    (r : K) (hr : r ∈ R) (hx : (x : K) = 1 + ϖ * r) : ((x⁻¹ : Kˣ) : K) ∈ R := by sorry
