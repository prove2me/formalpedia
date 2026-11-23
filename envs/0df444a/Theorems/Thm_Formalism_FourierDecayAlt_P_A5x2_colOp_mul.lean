-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_mul
-- name    : Formalism.FourierDecayAlt.P.A5x2.colOp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:31.497573+00:00
-- url     : https://prove2.me/theorems/a5a46a62-c4ca-4e16-809f-7c6d42889811
-- title:
--   A5x2: col Op mul
-- statement:
--   The A5x2 construction uses the col Op mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L146-L149

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

theorem Formalism.FourierDecayAlt.P.A5x2.colOp_mul (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K) (c : Fin n) (hZ : IsUnit Z.det) :
    Z * (1 + vecMulVec (Z⁻¹ *ᵥ m) (Pi.single c 1)) = Z + vecMulVec m (Pi.single c 1) := by sorry
