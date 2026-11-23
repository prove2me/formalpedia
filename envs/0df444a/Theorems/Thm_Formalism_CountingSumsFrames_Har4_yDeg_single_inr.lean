-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_yDeg_single_inr
-- name    : Formalism.CountingSumsFrames.Har4.yDeg_single_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:28.328203+00:00
-- url     : https://prove2.me/theorems/1cb7bd38-2d33-4fa1-bfbc-75f852dca41a
-- title:
--   Har4: y Deg single inr
-- statement:
--   The Har4 construction uses the y Deg single inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L497-L498
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L497-L498

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

theorem Formalism.CountingSumsFrames.Har4.yDeg_single_inr {k : ℕ} (i : Fin k) (n : ℕ) : yDeg (Finsupp.single (Sum.inr i : XY k) n) = n := by sorry
