-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_xDeg_single_inr
-- name    : Formalism.CountingSumsFrames.Har4.xDeg_single_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:21.849563+00:00
-- url     : https://prove2.me/theorems/f5c56251-4397-4fea-b733-2bb270a2c912
-- title:
--   Har4: x Deg single inr
-- statement:
--   The Har4 construction uses the x Deg single inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L493-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L493-L494

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

theorem Formalism.CountingSumsFrames.Har4.xDeg_single_inr {k : ℕ} (i : Fin k) (n : ℕ) : xDeg (Finsupp.single (Sum.inr i : XY k) n) = 0 := by sorry
