-- Prove2me | Theorems.Thm_ConnesGreen_prime_convolution_mass_bound
-- name    : ConnesGreen.prime_convolution_mass_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T00:41:45.28793+00:00
-- url     : https://prove2.me/theorems/e27261ca-dcb7-455b-8b59-5185c014ddb2
-- title:
--   Exact active prime contribution bounded by autocorrelation mass
-- statement:
--   Let $g:\mathbb R\to\mathbb C$ be an original smooth test supported in $[-T,T]$, and let $h=g*g^*$ with $g^*(t)=\overline{g(-t)}$. Put $M=\int|g|^2$ and $P_T=\sum_{n\in A_T}\Lambda(n)/\sqrt n$, where $A_T$ is the finite set of prime powers with $\log n<2T$. Then $$|\operatorname{Prime}(h)|\le 2P_T M.$$ The sum is the complete original prime contribution, with its strict support cutoff and vanishing von Mangoldt terms treated exactly. This unconditional estimate does not assert positivity of the Weil form.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/ArithmeticMassBudget.lean, declaration ConnesGreen.prime_convolution_mass_bound, compiling local source 8374c1d6419c567e9c1319e441c6a1348d0d0969. Original definitions and test class retained.

import Definitions.Def_ConnesGreen_arithmetic_mass_budget
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative

theorem ConnesGreen.prime_convolution_mass_bound (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) :
    ‖primeSum (conv g (starInv g))‖ ≤
      2 * activePrimeWeight T * (∫ s : ℝ, ‖g s‖ ^ 2) := by sorry
