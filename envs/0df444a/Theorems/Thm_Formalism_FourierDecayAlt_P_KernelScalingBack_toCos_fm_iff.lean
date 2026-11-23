-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_toCos_fm_iff
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.toCos_fm_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:44.747646+00:00
-- url     : https://prove2.me/theorems/9f3799c8-d368-40ae-be84-8227748ad180
-- title:
--   Kernel Scaling Back: to Cos fm iff
-- statement:
--   The Kernel Scaling Back construction uses the to Cos fm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L166-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L166-L185

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
variable (hc : ∀ b, ((c b : Kˣ) : K) ∈ R ∧ (((c b)⁻¹ : Kˣ) : K) ∈ R)
include hc

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.toCos_fm_iff (p p₁ : lowW K S T × upUniG K S.sum) :
    A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c p) =
        A5x8.toCos R (w := ((S, T * c) : Point K)) (fm S T c p₁) ↔
      A5x8.toCos R (w := ((S, T) : Point K)) p = A5x8.toCos R (w := ((S, T) : Point K)) p₁ := by sorry
