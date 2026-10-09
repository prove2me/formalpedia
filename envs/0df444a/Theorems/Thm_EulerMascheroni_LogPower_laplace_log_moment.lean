-- Prove2me | Theorems.Thm_EulerMascheroni_LogPower_laplace_log_moment
-- name    : EulerMascheroni.LogPower.laplace_log_moment
-- status  : Open
-- author  : @shivm
-- created : 2026-10-09T09:32:20.059975+00:00
-- url     : https://prove2.me/theorems/edd07f08-78f4-435f-9f6d-0f1a16024758
-- title:
--   $\int_0^\infty e^{-su}u^m\log u\,du=m!\,(H_m-\gamma-\log s)/s^{m+1}$
-- statement:
--   For every natural number $m$ and every real $s>0$,
--   $$\int_0^\infty e^{-su}\,u^m\log u\,du=\frac{m!\,\bigl(H_m-\gamma-\log s\bigr)}{s^{m+1}},$$
--   where $H_m=\sum_{j=1}^m 1/j$ is the $m$-th harmonic number and $\gamma$ is Euler's constant. Equivalently $\psi(m+1)=H_m-\gamma$, so the bracket is $\psi(m+1)-\log s$.
--
--   This is the engine behind a family of bounded-support functionals carrying $\gamma$. Substituting $t=e^{-u}$ turns it into
--   $$\int_0^1 t^{k}\cdot t^{a-1}\bigl(\log(1/t)\bigr)^m\bigl(-\log\log(1/t)\bigr)\,dt=\frac{m!\bigl(\gamma+\log(k+a)-H_m\bigr)}{(k+a)^{m+1}},$$
--   exhibiting moments of the form (rational) $+$ (rational)$\cdot\gamma$ together with a parasitic $\log(k+a)$ term. The $m=0$, $a=1$ case is the classical $\int_0^1 t^k(-\log\log(1/t))\,dt=(\gamma+\log(k+1))/(k+1)$.
-- source:
--   Standard Frullani/Laplace-transform identity; e.g. Gradshteyn-Ryzhik 4.352.1, and psi(m+1) = H_m - gamma (Abramowitz-Stegun 6.3.2). Used as the moment engine for Euler-constant Hankel data.

import Mathlib
open MeasureTheory

theorem EulerMascheroni.LogPower.laplace_log_moment (m : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫ u in Set.Ioi (0:ℝ), Real.exp (-s * u) * u ^ m * Real.log u
      = (Nat.factorial m : ℝ) * ((harmonic m : ℝ) - Real.eulerMascheroniConstant - Real.log s) / s ^ (m + 1) := by
  sorry
