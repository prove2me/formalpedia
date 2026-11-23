-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_xDeg_single_inl
-- name    : Formalism.CountingSumsFrames.Har4.xDeg_single_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:14.302647+00:00
-- url     : https://prove2.me/theorems/5de833d9-5870-479f-a368-e29475ef1b4e
-- title:
--   Har4: x Deg single inl
-- statement:
--   The Har4 construction uses the x Deg single inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L491-L492
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L491-L492

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

theorem Formalism.CountingSumsFrames.Har4.xDeg_single_inl {k : ℕ} (i : Fin k) (n : ℕ) : xDeg (Finsupp.single (Sum.inl i : XY k) n) = n := by sorry
