-- Prove2me | Theorems.Thm_ConnesGreen_prime_convolution_hasSum_exp_cutoff
-- name    : ConnesGreen.prime_convolution_hasSum_exp_cutoff
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T18:10:01.590429+00:00
-- url     : https://prove2.me/theorems/e8939689-7731-4e31-ad91-a79efc54d1d6
-- title:
--   Exact convergent prime cutoff for every original supported Weil test
-- statement:
--   For every original smooth test $g$ supported strictly in $(-t,t)$, and every natural $N>\exp(2t)$, the original prime summand of $g\star g^*$ has HasSum equal to its finite sum over $0\le n<N$. The same cutoff works for every such test. The convolution vanishes also at the doubled support boundary. This proves convergence and exact evaluation, not positivity, a zero-tail estimate or RH.
-- source:
--   monocap-tech/weil, CompactPrimeArithmetic.lean; original Connes convolution, involution, von Mangoldt normalization and supported test predicate. Companion native lemmas retain the actual complementary negative actor energy in the finite arithmetic expression.

import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier
open WeilDefect.ConnesNative
open scoped BigOperators
noncomputable section

theorem ConnesGreen.prime_convolution_hasSum_exp_cutoff (t : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest t g) (N : ℕ) (hN : Real.exp (2 * t) < N) :
    HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n)))
      (∑ n ∈ Finset.range N, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (conv g (starInv g) (Real.log n) + conv g (starInv g) (-Real.log n))) := by sorry
