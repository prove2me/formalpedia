-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_det
-- name    : Formalism.FourierDecayAlt.P.A5x2.colOp_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:52.913414+00:00
-- url     : https://prove2.me/theorems/a589f55c-82d9-41a9-b152-c52d7462eda9
-- title:
--   A5x2: col Op det
-- statement:
--   The A5x2 construction uses the col Op det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L165-L168

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.A5x2.colOp_det (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K) (c : Fin n) (hZ : IsUnit Z.det)
    (hξ : (Z⁻¹ *ᵥ m) c = 0) : IsUnit (Z + vecMulVec m (Pi.single c 1)).det := by sorry
