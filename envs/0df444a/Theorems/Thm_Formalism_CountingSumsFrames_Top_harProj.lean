-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Top_harProj
-- name    : Formalism.CountingSumsFrames.Top.harProj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:52.214705+00:00
-- url     : https://prove2.me/theorems/abb39e76-b02e-4999-8803-0f40a9f7e05c
-- title:
--   Top: har Proj
-- statement:
--   The Top construction uses the har Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/FinalHar.lean#L9-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/FinalHar.lean#L9-L9

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_FinalHar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top

theorem Formalism.CountingSumsFrames.Top.harProj : Formalism.CountingSumsFrames.HarProj := by sorry
