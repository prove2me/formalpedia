-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Top_borderedDetLinear
-- name    : Formalism.CountingSumsFrames.Top.borderedDetLinear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:49.267573+00:00
-- url     : https://prove2.me/theorems/e3a528eb-5a35-4935-9155-3392c0951143
-- title:
--   Top: bordered Det Linear
-- statement:
--   The Top construction uses the bordered Det Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/DetMulEqSumAdjugate.lean#L136-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/DetMulEqSumAdjugate.lean#L136-L157

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top

theorem Formalism.CountingSumsFrames.Top.borderedDetLinear : Formalism.CountingSumsFrames.BorderedDetLinear := by sorry
