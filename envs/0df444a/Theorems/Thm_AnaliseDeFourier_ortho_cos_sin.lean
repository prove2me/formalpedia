-- Prove2me | Theorems.Thm_AnaliseDeFourier_ortho_cos_sin
-- name    : AnaliseDeFourier.ortho_cos_sin
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:42:27.69943+00:00
-- url     : https://prove2.me/theorems/f81caf1c-edf0-426a-887a-0bf4acd6dc99
-- title:
--   Orthogonality relations: $\int_0^T \cos(\omega_n t)\sin(\omega_m t)\,dt = 0$
-- statement:
--   This is the third orthogonality relation of the trigonometric system, eq. (3.11c).
--
--   Let $T>0$ and let $n,m$ be non-negative integers, with $\omega_k = 2\pi k/T$. Then
--
--   $$\int_0^T \cos(\omega_n t)\,\sin(\omega_m t)\,dt = 0 ,$$
--
--   for every pair of indices, equal or not, including $n=m=0$. Cosines and sines of the harmonics are thus orthogonal to each other on a full period, which is what decouples the $a_n$ from the $b_n$ in the coefficient formulas.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Teorema 3.2.1, eq. (3.11c), p. 18

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem ortho_cos_sin (T : ℝ) (hT : 0 < T) (n m : ℕ) :
    (∫ t in (0 : ℝ)..T, Real.cos (angFreq T (n : ℤ) * t) * Real.sin (angFreq T (m : ℤ) * t))
      = 0 := by sorry

end AnaliseDeFourier
