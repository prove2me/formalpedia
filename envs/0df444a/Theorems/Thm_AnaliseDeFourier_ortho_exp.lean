-- Prove2me | Theorems.Thm_AnaliseDeFourier_ortho_exp
-- name    : AnaliseDeFourier.ortho_exp
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:43:05.718482+00:00
-- url     : https://prove2.me/theorems/cd8685ac-86c4-425d-9a89-4d5b144ea7d4
-- title:
--   Orthogonality in exponential form: $\int_0^T e^{i\omega_n t}e^{-i\omega_m t}\,dt$
-- statement:
--   This is the orthogonality relation of the trigonometric system in the exponential form used in §4.2 to pass from the $(a_n,b_n)$ representation to the $C_n$ representation.
--
--   Let $T>0$ and let $n,m$ be integers, with $\omega_k = 2\pi k/T$. Then
--
--   $$\int_0^T e^{i\omega_n t}\,e^{-i\omega_m t}\,dt = \begin{cases} T, & n = m,\\ 0, & n \neq m.\end{cases}$$
--
--   Unlike the trigonometric relations (3.11), which the book states for non-negative indices, this one runs over all of $\mathbb{Z}$, which is the index set of the exponential coefficients $C_n$. It is the computation behind the coefficient formula $C_n = \frac1T\int_0^T f(t)e^{-i\omega_n t}\,dt$ and behind Parseval's identity.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Sec. 4.2 (Forma exponencial), eqs. (4.5)-(4.8), pp. 30-31; exponential counterpart of Teorema 3.2.1 (eqs. 3.11), p. 18

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem ortho_exp (T : ℝ) (hT : 0 < T) (n m : ℤ) :
    (∫ t in (0 : ℝ)..T, Complex.exp (Complex.I * (angFreq T n * t))
        * Complex.exp (-(Complex.I * (angFreq T m * t))))
      = if n = m then (T : ℂ) else 0 := by sorry

end AnaliseDeFourier
