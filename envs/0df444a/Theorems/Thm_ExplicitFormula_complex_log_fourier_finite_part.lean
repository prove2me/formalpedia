-- Prove2me | Theorems.Thm_ExplicitFormula_complex_log_fourier_finite_part
-- name    : ExplicitFormula.complex_log_fourier_finite_part
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:47.990287+00:00
-- url     : https://prove2.me/theorems/47886f7f-0b57-4c92-b43a-d07a252e6fa8
-- title:
--   Fourier transform of $\log|z|^2$ on $\mathbb C$: $-\tfrac1\pi\,\mathrm{f.p.}\,|z|^{-2}-2(\gamma+\log\pi)\,\delta_0$ (Proposition B.4.3.2(2), corrected)
-- statement:
--   **Fourier transform of $\log|z|^2$ on the complex plane** (Proposition B.4.3.2(2), in corrected form).
--
--   Identify $\mathbb C$ with $\mathbb R^2$, let $dA$ be Lebesgue measure and, for a Schwartz function $f\in\mathcal S(\mathbb C)$, let
--   $$\widehat f(w)=\int_{\mathbb C}f(z)\,e^{-2\pi i\operatorname{Re}(z\bar w)}\,dA(z)$$
--   be its Fourier transform. The function $w\mapsto\log|w|^2$ is locally integrable and of slow growth, hence a tempered distribution on $\mathbb C$. Its Fourier transform is the sum of a finite part of $|z|^{-2}$ and a multiple of the Dirac mass at $0$: for every $f\in\mathcal S(\mathbb C)$ the limit on the right exists and
--   $$\int_{\mathbb C}\log|w|^2\,\widehat f(w)\,dA(w)=-\frac1\pi\lim_{\delta\to0^+}\left(\int_{|z|\ge\delta}\frac{f(z)}{|z|^2}\,dA(z)+2\pi f(0)\log\delta\right)-2(\gamma+\log\pi)\,f(0),$$
--   where $\gamma$ is the Euler–Mascheroni constant.
--
--   This is the Archimedean complex case of Connes' computation of the Fourier transform of $\log|\cdot|_v$ on a local field, which produces the principal values in Weil's explicit formulas (Definition B.4.4.1 of the source). The real case, $\int_{\mathbb R}\log|\xi|\,\widehat f(\xi)\,d\xi=-\tfrac12\lim_{\delta\to0^+}\big(\int_{|x|\ge\delta}f(x)\,\frac{dx}{|x|}+2f(0)\log\delta\big)-(\gamma+\log2\pi)f(0)$, is the platform theorem `MasulloAudit.real_log_fourier_exact_finite_part`.
--
--   **Deviation from the source.** In the normalization of the source — additive character $z\mapsto e^{-2\pi i\operatorname{Tr}_{\mathbb C/\mathbb R}(z)}$, self-dual measure $\nu=|dz\wedge d\bar z|=2\,dA$, $J(z)=\log|z|_v=\log|z|^2$, and $\langle\widehat J,f\rangle=\int J\,\widehat f\,d\nu$ — the identity above reads
--   $$\langle\widehat J,f\rangle=-\frac1{2\pi}\lim_{\varepsilon\to0^+}\left(\int_{|z|^2\ge\varepsilon}f(z)\,\frac{d\nu(z)}{|z|^2}+2\pi f(0)\log\varepsilon\right)-2\big(\log(2\pi)+\gamma\big)f(0).$$
--   Equation (B.4.3.14) prints the right-hand side multiplied by $2\pi$ (footnote 16 of the source flags these factors as unchecked; the real case (B.4.3.13) is likewise printed with an extra factor $2$). The statement formalized is the correct identity, written with Mathlib's Fourier transform on $\mathbb C\cong\mathbb R^2$.
--
--   **Formalization Note.** `f : SchwartzMap ℂ ℂ`, `FourierTransform.fourier` is Mathlib's Fourier transform on the real inner product space $\mathbb C$ (phase $e^{-2\pi i\langle z,w\rangle}$ with $\langle z,w\rangle=\operatorname{Re}(z\bar w)$, Lebesgue measure `volume`), and the statement is the convergence, as $\delta\to0^+$ (filter `𝓝[>] 0`), of $\int_{|z|\ge\delta}f(z)|z|^{-2}\,dA+2\pi f(0)\log\delta$ to $-\pi\int\log|w|^2\,\widehat f(w)\,dA(w)-2\pi(\gamma+\log\pi)f(0)$, which is the displayed identity multiplied by $-\pi$. The passage from the source's normalization uses $\widehat f_{\rm source}(w)=2\widehat f(2\bar w)$, which shifts the constant by $\log4$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 619, Proposition B.4.3.2(2), eq. (B.4.3.14), in the corrected form recorded in the statement; classical reference: A. Connes, Trace Formula in Noncommutative Geometry and the Zeros of the Riemann Zeta Function, Selecta Mathematica 5 (1999), Appendix II, eqs. (41), (42), p. 75 (as cited by the paper)

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace ExplicitFormula

theorem complex_log_fourier_finite_part (f : SchwartzMap ℂ ℂ) :
    Tendsto
      (fun δ : ℝ => (∫ z in {z : ℂ | δ ≤ ‖z‖}, f z / ((‖z‖ ^ 2 : ℝ) : ℂ)) +
        2 * π * f 0 * (Real.log δ : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(π : ℂ) * (∫ w : ℂ, (Real.log (‖w‖ ^ 2) : ℂ) *
          FourierTransform.fourier (f : ℂ → ℂ) w) -
        2 * π * ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) * f 0)) := by sorry

end ExplicitFormula
