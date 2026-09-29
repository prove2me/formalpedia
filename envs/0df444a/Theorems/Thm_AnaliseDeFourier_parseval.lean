-- Prove2me | Theorems.Thm_AnaliseDeFourier_parseval
-- name    : AnaliseDeFourier.parseval
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T22:08:40.54699+00:00
-- url     : https://prove2.me/theorems/ceece72e-f145-4e7e-bbcf-8c9dc99bfd48
-- title:
--   Teorema de Parseval: $\frac{1}{T}\int_0^T |f|^2\,dt = \sum_{n\in\mathbb{Z}} |C_n|^2$
-- statement:
--   This is Parseval's theorem for Fourier series, the capstone of the book's chapter 5.
--
--   Let $T>0$ and let $f:\mathbb{R}\to\mathbb{C}$ be a continuous $T$-periodic signal. Writing $\omega_n = 2\pi n/T$, its exponential Fourier coefficients are
--
--   $$C_n = \frac{1}{T}\int_0^T f(t)\,e^{-i\omega_n t}\,dt, \qquad n \in \mathbb{Z},$$
--
--   and its average power (Definição 5.1.1) is $P_f = \frac1T\int_0^T |f(t)|^2\,dt$. Then
--
--   $$\frac{1}{T}\int_0^{T} |f(t)|^{2}\,dt \;=\; \sum_{n=-\infty}^{\infty} |C_n|^{2}.$$
--
--   The average power of a periodic signal is thus the sum of the powers carried by its individual harmonics, which is the quantitative content of the frequency-domain picture and the basis of the RMS computations in the book's examples.
--
--   **Formalization Note.** The book states the theorem for a periodic function "representable by a Fourier series"; continuity is used here as the concrete sufficient regularity hypothesis. The right-hand side is an unordered sum over $\mathbb{Z}$, so no particular order of summation is presupposed; its convergence is the subject of a separate milestone.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Teorema 5.1.1 (Teorema de Parseval), eq. (5.9), p. 37; average power: Definicao 5.1.1, eq. (5.1), p. 36; coefficients C_n: eq. (4.8), p. 30

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem parseval (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    avgPower T f = ∑' n : ℤ, ‖coeffC T f n‖ ^ 2 := by sorry

end AnaliseDeFourier
