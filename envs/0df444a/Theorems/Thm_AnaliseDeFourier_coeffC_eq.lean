-- Prove2me | Theorems.Thm_AnaliseDeFourier_coeffC_eq
-- name    : AnaliseDeFourier.coeffC_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:49:07.006188+00:00
-- url     : https://prove2.me/theorems/2ab0eae6-5899-459c-b475-db955a30172e
-- title:
--   Eq. (4.8): $C_n = (a_n - i b_n)/2$
-- statement:
--   This is the dictionary between the trigonometric and the exponential representations of a Fourier series, eq. (4.8).
--
--   Let $T>0$ and let $f:\mathbb{R}\to\mathbb{R}$ be integrable on $[0,T]$. With $\omega_n = 2\pi n/T$ and
--
--   $$a_n = \frac{2}{T}\int_0^T f(t)\cos(\omega_n t)\,dt,\qquad b_n = \frac{2}{T}\int_0^T f(t)\sin(\omega_n t)\,dt,\qquad C_n = \frac{1}{T}\int_0^T f(t)e^{-i\omega_n t}\,dt,$$
--
--   one has, for every integer $n$ (positive, negative or zero),
--
--   $$C_n = \frac{a_n - i\,b_n}{2}.$$
--
--   At $n=0$ this specializes to the book's $C_0 = a_0/2$ (eq. 4.9), since $b_0=0$. The identity is what lets the two forms of Parseval's theorem — the one in $|C_n|^2$ and the classical one in $a_n^2+b_n^2$ — be translated into each other.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Sec. 4.2, eq. (4.8) and eq. (4.9), p. 30

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem coeffC_eq (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 T) (n : ℤ) :
    coeffC T (fun t => (f t : ℂ)) n
      = ((coeffA T f n : ℂ) - Complex.I * (coeffB T f n : ℂ)) / 2 := by sorry

end AnaliseDeFourier
