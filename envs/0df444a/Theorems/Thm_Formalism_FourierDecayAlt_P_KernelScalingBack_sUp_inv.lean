-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_sUp_inv
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.sUp_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:44.061799+00:00
-- url     : https://prove2.me/theorems/eeb1bde0-c95f-483a-89dd-73a4a909745f
-- title:
--   Kernel Scaling Back: s Up inv
-- statement:
--   The Kernel Scaling Back construction uses the s Up inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L265-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L265-L270

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

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.sUp_inv (u : upUniG K n) :
    sUp (((u⁻¹ : upUniG K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      - sUp ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by sorry
