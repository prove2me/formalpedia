-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har4_multinomial_factorization_le
-- name    : Formalism.CountingSumsFrames.Har4.multinomial_factorization_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:26.691461+00:00
-- url     : https://prove2.me/theorems/8d1b55f8-0d5b-4be5-8ab8-f021bba48034
-- title:
--   Har4: multinomial factorization le
-- statement:
--   The Har4 construction uses the multinomial factorization le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L231-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/SqrtFockGaussLatticeComparisonHolds.lean#L231-L254

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

theorem Formalism.CountingSumsFrames.Har4.multinomial_factorization_le (p : ℕ) {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    (Nat.multinomial s f).factorization p ≤ (s.card - 1) * Nat.log p (∑ i ∈ s, f i) := by sorry
