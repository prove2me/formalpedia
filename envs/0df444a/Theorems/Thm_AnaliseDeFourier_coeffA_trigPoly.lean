-- Prove2me | Theorems.Thm_AnaliseDeFourier_coeffA_trigPoly
-- name    : AnaliseDeFourier.coeffA_trigPoly
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:43:28.207281+00:00
-- url     : https://prove2.me/theorems/fd0bd0cd-87bf-4902-ba94-6481bc6052a0
-- title:
--   Teorema 3.2.2: the formula $a_m = \frac{2}{T}\int_0^T f\cos(\omega_m t)\,dt$ recovers $a_m$
-- statement:
--   This is the cosine half of Teorema 3.2.2, in the finite (trigonometric polynomial) regime where no convergence hypothesis is needed.
--
--   Let $T>0$, let $a,b:\mathbb{Z}\to\mathbb{R}$ be coefficient families, let $N$ be a degree and let $0 \le m \le N$. Write $\omega_k = 2\pi k/T$ and let
--
--   $$f(t) = \frac{a_0}{2} + \sum_{n=1}^{N}\bigl[a_n\cos(\omega_n t) + b_n\sin(\omega_n t)\bigr].$$
--
--   Then the integral formula (3.23) returns the coefficient it should:
--
--   $$\frac{2}{T}\int_0^T f(t)\cos(\omega_m t)\,dt = a_m .$$
--
--   The case $m=0$ is included and reproduces the book's formula (3.23a) for $a_0$, in accordance with Observação 3.2.1: because $\cos 0 = 1$, the formula for $a_n$ at $n=0$ is the formula for $a_0$. This is the finite, hypothesis-free form of the book's derivation, which for an infinite series requires an unstated convergence assumption.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Teorema 3.2.2 and eq. (3.23a)-(3.23b), Observacao 3.2.1, pp. 19-20; trigonometric polynomial: Definicao 3.2.1, p. 17

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem coeffA_trigPoly (T : ℝ) (hT : 0 < T) (a b : ℤ → ℝ) (N m : ℕ) (hm : m ≤ N) :
    coeffA T (trigPoly T a b N) (m : ℤ) = a (m : ℤ) := by sorry

end AnaliseDeFourier
