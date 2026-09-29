-- Prove2me | Theorems.Thm_AnaliseDeFourier_coeffB_trigPoly
-- name    : AnaliseDeFourier.coeffB_trigPoly
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:45:03.922664+00:00
-- url     : https://prove2.me/theorems/a92a297b-7bde-4f20-860d-a2715477641f
-- title:
--   Teorema 3.2.2: the formula $b_m = \frac{2}{T}\int_0^T f\sin(\omega_m t)\,dt$ recovers $b_m$
-- statement:
--   This is the sine half of Teorema 3.2.2, in the finite (trigonometric polynomial) regime where no convergence hypothesis is needed.
--
--   Let $T>0$, let $a,b:\mathbb{Z}\to\mathbb{R}$, let $N$ be a degree and let $0 \le m \le N$. With $\omega_k = 2\pi k/T$ and
--
--   $$f(t) = \frac{a_0}{2} + \sum_{n=1}^{N}\bigl[a_n\cos(\omega_n t) + b_n\sin(\omega_n t)\bigr],$$
--
--   the integral formula (3.23c) returns
--
--   $$\frac{2}{T}\int_0^T f(t)\sin(\omega_m t)\,dt = \begin{cases} b_m, & 1 \le m \le N,\\ 0, & m = 0.\end{cases}$$
--
--   The value at $m=0$ is $0$ rather than $b_0$, in accordance with the book's convention $b_0 = 0$ (eq. 4.7): the function $\sin(\omega_0 t)$ is identically zero, so the coefficient $b_0$ of the polynomial is invisible to the formula.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Teorema 3.2.2 and eq. (3.23c), pp. 19-20; convention b_0 = 0: eq. (4.7), p. 30; trigonometric polynomial: Definicao 3.2.1, p. 17

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem coeffB_trigPoly (T : ℝ) (hT : 0 < T) (a b : ℤ → ℝ) (N m : ℕ) (hm : m ≤ N) :
    coeffB T (trigPoly T a b N) (m : ℤ) = if m = 0 then 0 else b (m : ℤ) := by sorry

end AnaliseDeFourier
