-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_xDeg_add
-- name    : Formalism.CountingSumsFrames.Har4.xDeg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:25.19328+00:00
-- url     : https://prove2.me/theorems/1e3d2abf-6cb1-45cb-80f7-e984a86a0710
-- title:
--   Har4: x Deg add
-- statement:
--   The Har4 construction uses the x Deg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L487-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L487-L488

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_xDeg_add

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

theorem Formalism.CountingSumsFrames.Har4.xDeg_add {k : ℕ} (m n : XY k →₀ ℕ) : xDeg (m + n) = xDeg m + xDeg n := by sorry
