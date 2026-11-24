-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_lip_triv
-- name    : Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.lip_triv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:21.026593+00:00
-- url     : https://prove2.me/theorems/5d963cfe-f8f4-48cb-a026-915a911a3d80
-- title:
--   AN: lip triv
-- statement:
--   The AN construction uses the lip triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L947-L953
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean#L947-L953

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN

theorem Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.lip_triv (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hw' : 0 < w') :
    |w * Gz (A / w) - w' * Gz (A / w')| ≤ 3 * A / min w w' * |w - w'| := by sorry
