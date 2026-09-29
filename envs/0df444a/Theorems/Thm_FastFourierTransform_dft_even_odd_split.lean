-- Prove2me | Theorems.Thm_FastFourierTransform_dft_even_odd_split
-- name    : FastFourierTransform.dft_even_odd_split
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:22:25.880197+00:00
-- url     : https://prove2.me/theorems/ffc67fdb-812d-4e6e-bff5-a3df1ec2c658
-- title:
--   Danielson–Lanczos even/odd splitting
-- statement:
--   **The Danielson–Lanczos lemma (even/odd splitting).** Let $N\ge 1$. For every signal $x$ and every frequency index $k$,
--
--   $$\mathrm{dft}(2N,x)(k)=\mathrm{dft}\big(N,\;m\mapsto x_{2m}\big)(k)+e^{-2\pi i k/(2N)}\,\mathrm{dft}\big(N,\;m\mapsto x_{2m+1}\big)(k).$$
--
--   A transform of even length $2N$ is the transform of its even-indexed samples plus a twiddle factor times the transform of its odd-indexed samples, both of length $N$. Note the change of denominator: the two transforms on the right use $e^{-2\pi i mk/N}$, the one on the left uses $e^{-2\pi i mk/(2N)}$. The index $k$ is not reduced modulo $N$ on the right-hand side. This identity is the single algebraic step on which every radix-2 Cooley–Tukey variant rests.
-- source:
--   Danielson & Lanczos 1942 (doubling step), as reported in Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, sections 'History' and 'Algorithms — Cooley–Tukey algorithm'

import Mathlib
import Definitions.Def_FastFourierTransform_dft

namespace FastFourierTransform

theorem dft_even_odd_split (N : ℕ) (hN : 0 < N) (x : ℕ → ℂ) (k : ℕ) :
    dft (2 * N) x k =
      dft N (fun m => x (2 * m)) k
        + Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / ((2 * N : ℕ) : ℂ)))
            * dft N (fun m => x (2 * m + 1)) k := by sorry

end FastFourierTransform
