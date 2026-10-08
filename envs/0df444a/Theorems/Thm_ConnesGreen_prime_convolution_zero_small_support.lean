-- Prove2me | Theorems.Thm_ConnesGreen_prime_convolution_zero_small_support
-- name    : ConnesGreen.prime_convolution_zero_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T00:44:52.443603+00:00
-- url     : https://prove2.me/theorems/2cb619e8-f131-490f-8309-86259205e7ce
-- title:
--   Full original prime convolution term vanishes at the first support threshold
-- statement:
--   For an unchanged original admissible test $g$ supported in $(-T,T)$, if $2T\le\log2$, then $$\operatorname{primeSum}(g*g^*)=0.$$ Equality at the threshold is included, and the complete original sum over all natural numbers is retained. The $n=0,1$ coefficients vanish by the original von Mangoldt values. For every $n\ge2$, $\log n\ge\log2\ge2T$; the accepted original overlap-energy bound proves both convolution values at $\pm\log n$ zero. Every actual summand therefore vanishes. No cutoff approximation, replacement prime sum, gamma hypothesis or positivity assertion is introduced.
-- source:
--   monocap-tech/weil at b0fd3ea4942154e083984fda035eff95e0a8de48; exact native signatures from SmallSupportPositivity.lean. Accepted original Mellin and overlap interfaces are reused. Native declarations are unchanged.

import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

theorem ConnesGreen.prime_convolution_zero_small_support (T : ℝ) (g : ℝ → ℂ)
    (hg : SupportedTest T g) (hT : 2 * T ≤ Real.log 2) :
    primeSum (conv g (starInv g)) = 0 := by sorry
