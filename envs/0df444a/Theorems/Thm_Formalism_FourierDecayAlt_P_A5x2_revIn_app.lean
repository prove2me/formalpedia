-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_revIn_app
-- name    : Formalism.FourierDecayAlt.P.A5x2.revIn_app
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:44.427928+00:00
-- url     : https://prove2.me/theorems/13748671-486d-4fc4-8149-de778a79a5ff
-- title:
--   A5x2: rev In app
-- statement:
--   The A5x2 construction uses the rev In app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L16-L20

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

theorem Formalism.FourierDecayAlt.P.A5x2.revIn_app (l : List ℕ) (s : ℕ) (hs : 1 ≤ s) :
    revIn (l ++ [s]) l.sum = l.sum + (s - 1) := by sorry
