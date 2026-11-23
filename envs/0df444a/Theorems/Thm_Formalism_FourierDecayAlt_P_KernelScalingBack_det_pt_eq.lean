-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_det_pt_eq
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.det_pt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:15.859153+00:00
-- url     : https://prove2.me/theorems/32b2740c-675a-4f68-82c8-dedda64f7196
-- title:
--   Kernel Scaling Back: det pt eq
-- statement:
--   The Kernel Scaling Back construction uses the det pt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L444-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L444-L461

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
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.det_pt_eq (s : List ℕ) : ∃ e : Kˣ, ∀ t : ℕ → Kˣ,
    (pt s t).det = (∏ a : Fin s.sum, ((t (blk s a) : Kˣ) : K)) * (e : K) := by sorry
