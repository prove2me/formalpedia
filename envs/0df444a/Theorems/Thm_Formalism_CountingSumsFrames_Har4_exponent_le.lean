-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_exponent_le
-- name    : Formalism.CountingSumsFrames.Har4.exponent_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:08.122865+00:00
-- url     : https://prove2.me/theorems/798296cc-77c4-4a9d-8b49-c4b2cbf04b68
-- title:
--   Har4: exponent le
-- statement:
--   The Har4 construction uses the exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L719-L762
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L719-L762

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

theorem Formalism.CountingSumsFrames.Har4.exponent_le {k A B a p e : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hA : A ≤ 8 * a) (hB : B ≤ 8 * a)
    (he : 3 * (Real.logb p (8 * (a : ℝ) + k - 1) + 1) + 4 * (k : ℝ) * (Real.logb p (8 * (a : ℝ) + k - 1) + 1)
      ≤ (e : ℝ)) : (k + 1) * Nat.log p (A + B + k) ≤ e := by sorry
