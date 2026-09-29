-- Prove2me | Theorems.Thm_AnaliseDeFourier_ortho_cos_cos
-- name    : AnaliseDeFourier.ortho_cos_cos
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:40:47.231975+00:00
-- url     : https://prove2.me/theorems/09963236-a144-4c32-afb7-4ce7980a393c
-- title:
--   Orthogonality relations: $\int_0^T \cos(\omega_n t)\cos(\omega_m t)\,dt$
-- statement:
--   This is the second orthogonality relation of the trigonometric system, eq. (3.11b).
--
--   Let $T>0$ and let $n,m$ be non-negative integers, with $\omega_k = 2\pi k/T$. Then
--
--   $$\int_0^T \cos(\omega_n t)\,\cos(\omega_m t)\,dt = \begin{cases} 0, & n \neq m,\\ T/2, & n = m \neq 0,\\ T, & n = m = 0.\end{cases}$$
--
--   The three cases are exactly those listed in the book. The distinguished value $T$ at $n=m=0$ is the reason the constant term of a Fourier series is written $a_0/2$ rather than $a_0$.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Teorema 3.2.1, eq. (3.11b), p. 18

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem ortho_cos_cos (T : ℝ) (hT : 0 < T) (n m : ℕ) :
    (∫ t in (0 : ℝ)..T, Real.cos (angFreq T (n : ℤ) * t) * Real.cos (angFreq T (m : ℤ) * t))
      = if n = m then (if n = 0 then T else T / 2) else 0 := by sorry

end AnaliseDeFourier
