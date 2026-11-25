-- Prove2me | Theorems.Thm_Arxiv2111_09089_laurent_series_on_annulus
-- name    : Arxiv2111_09089.laurent_series_on_annulus
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:36:54.212039+00:00
-- url     : https://prove2.me/theorems/09a8c64a-4fef-44b3-aa44-134b76970b40
-- title:
--   Eq. (5): Laurent series of the spectral function on an annulus around the unit circle
-- statement:
--   Let $0<\delta<1$ and let $g$ be holomorphic on the annulus $1-\delta<|\eta|<1+\delta$. For $n\in\mathbb Z$ let
--
--   $$c_n=\frac1{2\pi}\int_0^{2\pi}g(e^{j\phi})\,e^{-jn\phi}\,d\phi$$
--
--   be the Fourier coefficients of $g$ on the unit circle. Then for every $\eta$ in the annulus
--
--   $$g(\eta)=\sum_{n=-\infty}^{\infty}c_n\eta^n,$$
--
--   the series converging unconditionally. On $|\eta|=1$ this Laurent series is the Fourier series of $\phi\mapsto g(e^{j\phi})$, so its coefficients are the ones the paper computes by FFT.
--
--   **Formalization Note** The paper deduces holomorphy on the annulus from the absence of poles on the tilted path. Here holomorphy is a hypothesis. The point $\eta=1$ of the circle corresponds to $\xi=\infty$, where the spectral Green's function is in general not holomorphic (see REPORT).
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), claim c004; Section II-C, eq. (5) and the text after it, PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics

namespace Arxiv2111_09089

theorem laurent_series_on_annulus (g : ℂ → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hg : DifferentiableOn ℂ g (annulus δ)) :
    ∀ η ∈ annulus δ, HasSum (fun n : ℤ => laurentCoeff g n * η ^ n) (g η) := by sorry

end Arxiv2111_09089
