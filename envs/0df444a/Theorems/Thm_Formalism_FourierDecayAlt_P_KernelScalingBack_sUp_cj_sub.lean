-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_sUp_cj_sub
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.sUp_cj_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:23.889065+00:00
-- url     : https://prove2.me/theorems/997a7355-05ad-44af-961e-98f36be3c8cc
-- title:
--   Kernel Scaling Back: s Up cj sub
-- statement:
--   The Kernel Scaling Back construction uses the s Up cj sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L246-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L246-L263

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
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.sUp_cj_sub (d : Fin n → Kˣ) (y : GL (Fin n) K)
    (hB : ∀ (j : Fin n) (hj : j.val + 1 < n),
      ((((d j)⁻¹ : Kˣ) : K) * ((d ⟨j.val + 1, hj⟩ : Kˣ) : K) - 1) *
        (y : Matrix (Fin n) (Fin n) K) j ⟨j.val + 1, hj⟩ ∈ R) :
    sUp ((cj d y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      sUp (y : Matrix (Fin n) (Fin n) K) ∈ R := by sorry
