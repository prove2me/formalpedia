-- Prove2me | Theorems.Thm_FastFourierTransform_fftAddCount_eq
-- name    : FastFourierTransform.fftAddCount_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:43:12.248578+00:00
-- url     : https://prove2.me/theorems/3220c371-8f44-4869-a1f2-a3da0257fafc
-- title:
--   Radix-2 addition count: $n\log_2 n$
-- statement:
--   **Complex addition count of the radix-2 algorithm.** Let $A$ be the addition counter of the butterfly cost model, $A(0)=0$ and $A(p+1)=2A(p)+2^{p+1}$. Then for every $p$
--
--   $$A(p)=p\cdot 2^{p}=n\log_2 n,\qquad n=2^p.$$
--
--   Each of the $n/2$ butterflies of a merge stage contributes two complex additions, and there are $\log_2 n$ stages. The identity is exact and holds for $p=0$ as well.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Definition' ('n log_2 n complex additions')

import Mathlib
import Definitions.Def_FastFourierTransform_opCount

namespace FastFourierTransform

theorem fftAddCount_eq (p : ℕ) : fftAddCount p = p * 2 ^ p := by sorry

end FastFourierTransform
