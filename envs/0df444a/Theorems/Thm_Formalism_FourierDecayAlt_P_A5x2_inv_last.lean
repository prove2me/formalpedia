-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_inv_last
-- name    : Formalism.FourierDecayAlt.P.A5x2.inv_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:41.533674+00:00
-- url     : https://prove2.me/theorems/160fb546-cf90-4bb2-834a-219adb133ee6
-- title:
--   A5x2: inv last
-- statement:
--   The A5x2 construction uses the inv last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L22-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L22-L43

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

theorem Formalism.FourierDecayAlt.P.A5x2.inv_last {K : Type} [CommRing K] (S : List ℕ) (T : ℕ → Kˣ)
    (x y : Matrix (Fin S.sum) (Fin S.sum) K) (hx : IsLowUni x) (hy : IsUpUni y)
    (a b c : Fin S.sum) (hb : b.val + 1 = S.sum) (hc : revF S c = b) :
    (x * pt S T * y)⁻¹ a b = (((T (blk S c))⁻¹ : Kˣ) : K) * y⁻¹ a c := by sorry
