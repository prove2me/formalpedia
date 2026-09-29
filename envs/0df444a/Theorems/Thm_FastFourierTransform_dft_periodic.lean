-- Prove2me | Theorems.Thm_FastFourierTransform_dft_periodic
-- name    : FastFourierTransform.dft_periodic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:17:12.792759+00:00
-- url     : https://prove2.me/theorems/1ca22665-cd8d-49a1-ba07-afcfff0ee929
-- title:
--   The DFT is $n$-periodic in the frequency index
-- statement:
--   **Periodicity of the DFT in the frequency index.** For every length $n$, every signal $x$ and every index $k$,
--
--   $$\mathrm{dft}(n,x)(k+n)=\mathrm{dft}(n,x)(k),$$
--
--   because $e^{-2\pi i\,m(k+n)/n}=e^{-2\pi i\,mk/n}e^{-2\pi i m}=e^{-2\pi i\,mk/n}$ for integer $m$. The case $n=0$ is included and both sides are then the empty sum $0$. This periodicity is what lets the Cooley–Tukey recursion evaluate its sub-transforms at the reduced index $k \bmod 2^p$.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Definition' (the DFT is defined for indices modulo n)

import Mathlib
import Definitions.Def_FastFourierTransform_dft

namespace FastFourierTransform

theorem dft_periodic (n : ℕ) (x : ℕ → ℂ) (k : ℕ) :
    dft n x (k + n) = dft n x k := by sorry

end FastFourierTransform
