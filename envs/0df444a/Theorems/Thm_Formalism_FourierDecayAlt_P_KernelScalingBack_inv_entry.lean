-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_inv_entry
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.inv_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:06.337106+00:00
-- url     : https://prove2.me/theorems/865cf180-5a6f-449d-bebd-0ba0cc65219c
-- title:
--   Kernel Scaling Back: inv entry
-- statement:
--   The Kernel Scaling Back construction uses the inv entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L345-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L345-L348

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

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.inv_entry {n : ℕ} {Z : Matrix (Fin n) (Fin n) K} (hZ : IsInt R Z) {x : K}
    (hx : x * Ring.inverse Z.det ∈ R) (a b : Fin n) : x * Z⁻¹ a b ∈ R := by sorry
