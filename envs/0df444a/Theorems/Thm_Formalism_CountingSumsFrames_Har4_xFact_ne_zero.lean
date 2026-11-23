-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_xFact_ne_zero
-- name    : Formalism.CountingSumsFrames.Har4.xFact_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:29.862471+00:00
-- url     : https://prove2.me/theorems/d40d50c6-fe4f-4013-9526-c2ddeff7dc1c
-- title:
--   Har4: x Fact ne zero
-- statement:
--   The Har4 construction uses the x Fact ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L283-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L283-L284

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

theorem Formalism.CountingSumsFrames.Har4.xFact_ne_zero {k : ℕ} (m : XY k →₀ ℕ) : xFact m ≠ 0 := by sorry
