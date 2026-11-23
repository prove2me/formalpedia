-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_add_single_mulVec
-- name    : Formalism.FourierDecayAlt.P.A5x2.add_single_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:26.887639+00:00
-- url     : https://prove2.me/theorems/b646da0a-0ea7-4be1-bfab-795f201094b5
-- title:
--   A5x2: add single mul Vec
-- statement:
--   The A5x2 construction uses the add single mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L170-L175

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

theorem Formalism.FourierDecayAlt.P.A5x2.add_single_mulVec (Z : Matrix (Fin n) (Fin n) K) (m y : Fin n → K) (c : Fin n) :
    (Z + vecMulVec m (Pi.single c 1)) *ᵥ y = Z *ᵥ y + y c • m := by sorry
