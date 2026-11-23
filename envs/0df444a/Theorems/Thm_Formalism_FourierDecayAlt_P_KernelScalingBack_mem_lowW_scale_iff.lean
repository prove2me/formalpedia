-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_mem_lowW_scale_iff
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.mem_lowW_scale_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:28.016394+00:00
-- url     : https://prove2.me/theorems/87861ae8-b965-46e6-b24b-8bcd7e5c9112
-- title:
--   Kernel Scaling Back: mem low W scale iff
-- statement:
--   The Kernel Scaling Back construction uses the mem low W scale iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L131-L134

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
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.mem_lowW_scale_iff {g : GL (Fin S.sum) K} : g ∈ lowW K S (T * c) ↔ g ∈ lowW K S T := by sorry
