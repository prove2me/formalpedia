-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_weight_wXY
-- name    : Formalism.CountingSumsFrames.Har4.weight_wXY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:20.238019+00:00
-- url     : https://prove2.me/theorems/0c8e6518-53dc-433a-a17d-7b71de6e8c10
-- title:
--   Har4: weight w XY
-- statement:
--   The Har4 construction uses the weight w XY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L163-L165

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4

theorem Formalism.CountingSumsFrames.Har4.weight_wXY {k : ℕ} (m : XY k →₀ ℕ) : Finsupp.weight (wXY k) m = (xDeg m, yDeg m) := by sorry
