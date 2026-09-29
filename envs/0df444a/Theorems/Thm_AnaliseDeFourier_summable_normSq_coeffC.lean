-- Prove2me | Theorems.Thm_AnaliseDeFourier_summable_normSq_coeffC
-- name    : AnaliseDeFourier.summable_normSq_coeffC
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T21:05:32.831014+00:00
-- url     : https://prove2.me/theorems/4b040325-4215-4db3-b421-6ce905b57095
-- title:
--   Summability of $\bigl(|C_n|^2\bigr)_{n \in \mathbb{Z}}$
-- statement:
--   This makes the right-hand side of Parseval's identity (Teorema 5.1.1) meaningful.
--
--   Let $T>0$ and let $f:\mathbb{R}\to\mathbb{C}$ be continuous, with exponential Fourier coefficients $C_n = \frac1T\int_0^T f(t)e^{-i\omega_n t}\,dt$, $n \in \mathbb{Z}$. Then the family
--
--   $$\bigl(|C_n|^2\bigr)_{n \in \mathbb{Z}}$$
--
--   is summable: its unordered sum over $\mathbb{Z}$ converges, so in particular the doubly infinite series $\sum_{n=-\infty}^{\infty}|C_n|^2$ has a value that does not depend on the order of summation. The book writes this series without comment; the formal development records its convergence as a separate statement.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, supporting step for Teorema 5.1.1 (Teorema de Parseval), eq. (5.9), p. 37

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem summable_normSq_coeffC (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hf : Continuous f) :
    Summable (fun n : ℤ => ‖coeffC T f n‖ ^ 2) := by sorry

end AnaliseDeFourier
