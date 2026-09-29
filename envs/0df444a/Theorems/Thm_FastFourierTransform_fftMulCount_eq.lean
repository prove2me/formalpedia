-- Prove2me | Theorems.Thm_FastFourierTransform_fftMulCount_eq
-- name    : FastFourierTransform.fftMulCount_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:37:13.253614+00:00
-- url     : https://prove2.me/theorems/b5c8f203-14fe-4eb4-a7e6-f7e2590bbcd4
-- title:
--   Radix-2 multiplication count: $\frac n2\log_2 n$
-- statement:
--   **Complex multiplication count of the radix-2 algorithm.** Let $M$ be the multiplication counter of the butterfly cost model, $M(0)=0$ and $M(p+1)=2M(p)+2^p$. Then for every $p$
--
--   $$2M(p)=p\cdot 2^{p},\qquad\text{i.e.}\qquad M(p)=\frac n2\log_2 n \text{ with } n=2^p.$$
--
--   The statement is given in the doubled form to stay inside natural-number arithmetic (no division, no subtraction), and the case $p=0$ is included. This is the exact count of twiddle-factor multiplications, not an asymptotic bound.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Definition' ('(n/2)log_2 n complex multiplications')

import Mathlib
import Definitions.Def_FastFourierTransform_opCount

namespace FastFourierTransform

theorem fftMulCount_eq (p : ℕ) : 2 * fftMulCount p = p * 2 ^ p := by sorry

end FastFourierTransform
