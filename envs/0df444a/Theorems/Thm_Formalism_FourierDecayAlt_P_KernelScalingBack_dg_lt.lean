-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_dg_lt
-- name    : Formalism.FourierDecayAlt.P.KernelScalingBack.dg_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:03.535863+00:00
-- url     : https://prove2.me/theorems/4a609e82-6a57-4bf6-9d3b-4f6b55cea369
-- title:
--   Kernel Scaling Back: dg lt
-- statement:
--   The Kernel Scaling Back construction uses the dg lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L368-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean#L368-L372

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

theorem Formalism.FourierDecayAlt.P.KernelScalingBack.dg_lt (l : List ℕ) (s : ℕ) (k : Kˣ) (j : Fin (l ++ [s]).sum) (hj : j.val < l.sum) :
    dg (l ++ [s]) (Function.update (1 : ℕ → Kˣ) l.length k) j = 1 := by sorry
