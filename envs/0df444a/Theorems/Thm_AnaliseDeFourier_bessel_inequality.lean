-- Prove2me | Theorems.Thm_AnaliseDeFourier_bessel_inequality
-- name    : AnaliseDeFourier.bessel_inequality
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T20:49:27.968215+00:00
-- url     : https://prove2.me/theorems/c1d8ea77-f521-4e14-a51a-4c975639f5d8
-- title:
--   Bessel's inequality: $\sum_{n \in s} |C_n|^2 \le P_f$ for every finite $s \subseteq \mathbb{Z}$
-- statement:
--   This is Bessel's inequality for the exponential Fourier coefficients: the half of Parseval's identity (Teorema 5.1.1) that holds without any convergence assumption.
--
--   Let $T>0$ and let $f:\mathbb{R}\to\mathbb{C}$ be continuous. With $C_n = \frac1T\int_0^T f(t)e^{-i\omega_n t}\,dt$ and average power $P_f = \frac1T\int_0^T |f(t)|^2\,dt$, for every finite set $s$ of integers
--
--   $$\sum_{n \in s} |C_n|^2 \;\le\; P_f .$$
--
--   In words: no finite collection of harmonics can carry more than the total average power of the signal. Parseval's theorem is the statement that, summing over all of $\mathbb{Z}$, equality is attained; this inequality is the easy direction and also supplies the summability needed to make the infinite sum meaningful.
-- source:
--   Esequia Sauter, Fabio Souto de Azevedo (orgs.), Analise de Fourier - Um Livro Colaborativo, UFRGS/REAMAT, 26 July 2022, https://www.ufrgs.br/reamat/TransformadasIntegrais/livro-af/main.html, supporting step for Teorema 5.1.1 (Teorema de Parseval), eq. (5.9), p. 37; average power: Definicao 5.1.1, eq. (5.1), p. 36

import Mathlib
import Definitions.Def_analise_de_fourier_core

open MeasureTheory

namespace AnaliseDeFourier

theorem bessel_inequality (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hf : Continuous f) (s : Finset ℤ) :
    ∑ n ∈ s, ‖coeffC T f n‖ ^ 2 ≤ avgPower T f := by sorry

end AnaliseDeFourier
