-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_phase_fm
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.phase_fm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:21.416323+00:00
-- url     : https://prove2.me/theorems/926e62fa-92a9-47a6-810f-6279ab22d326
-- title:
--   Kernel Scaling Back: phase fm
-- statement:
--   The Kernel Scaling Back construction uses the phase fm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L278-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L278-L300

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

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.phase_fm (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (p : lowW K S T × upUniG K S.sum)
    (hB : ∀ (j : Fin S.sum) (hj : j.val + 1 < S.sum),
      ((((dg S c j)⁻¹ : Kˣ) : K) * ((dg S c ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (((p.2⁻¹ : upUniG K S.sum) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) j
          ⟨j.val + 1, hj⟩ ∈ R) :
    phase ψ (w := ((S, T * c) : Point K)) (fm S T c p) = phase ψ (w := ((S, T) : Point K)) p := by sorry
