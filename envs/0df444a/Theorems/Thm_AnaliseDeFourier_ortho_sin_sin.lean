-- Prove2me | Theorems.Thm_AnaliseDeFourier_ortho_sin_sin
-- name    : AnaliseDeFourier.ortho_sin_sin
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:38:11.593838+00:00
-- url     : https://prove2.me/theorems/7d0e0ade-093d-4d0c-9c4f-573b51bb08c9
-- title:
--   Orthogonality relations: $\int_0^T \sin(\omega_n t)\sin(\omega_m t)\,dt$
-- statement:
--   This is the first orthogonality relation of the trigonometric system, eq. (3.11a).
--
--   Let $T>0$ and let $n,m$ be non-negative integers, with $\omega_k = 2\pi k/T$. Then
--
--   $$\int_0^T \sin(\omega_n t)\,\sin(\omega_m t)\,dt = \begin{cases} T/2, & n = m \neq 0,\\ 0, & \text{otherwise.}\end{cases}$$
--
--   The book lists the two cases $n\neq m$ (value $0$) and $n=m\neq0$ (value $T/2$); the remaining index pair $n=m=0$ makes the integrand identically zero, so the value $0$ is recorded for it as well. Together with the two companion relations this expresses that the sines and cosines of the fundamental frequency and its harmonics are pairwise orthogonal on a full period, which is what makes the Fourier coefficient formulas work.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, Teorema 3.2.1, eq. (3.11a), p. 18

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem ortho_sin_sin (T : ℝ) (hT : 0 < T) (n m : ℕ) :
    (∫ t in (0 : ℝ)..T, Real.sin (angFreq T (n : ℤ) * t) * Real.sin (angFreq T (m : ℤ) * t))
      = if n = m ∧ n ≠ 0 then T / 2 else 0 := by sorry

end AnaliseDeFourier
