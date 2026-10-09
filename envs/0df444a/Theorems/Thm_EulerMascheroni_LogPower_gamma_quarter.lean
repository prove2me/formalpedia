-- Prove2me | Theorems.Thm_EulerMascheroni_LogPower_gamma_quarter
-- name    : EulerMascheroni.LogPower.gamma_quarter
-- status  : Open
-- author  : @shivm
-- created : 2026-10-09T09:32:04.797694+00:00
-- url     : https://prove2.me/theorems/682d4f65-956e-4f6d-bf24-999036b554a5
-- title:
--   $\int_0^\infty (e^{-2u}-e^{-4u})(-\log u)\,du=\gamma/4$
-- statement:
--   $$\int_0^\infty\bigl(e^{-2u}-e^{-4u}\bigr)\bigl(-\log u\bigr)\,du=\frac{\gamma}{4}.$$
--
--   Equivalently, substituting $t=e^{-u}$,
--   $$\int_0^1 (t-t^3)\bigl(-\log\log(1/t)\bigr)\,dt=\frac{\gamma}{4}.$$
--
--   This is the smallest instance of a log-free representation of a rational multiple of $\gamma$. The moments $\int_0^1 t^k(-\log\log(1/t))\,dt=(\gamma+\log(k+1))/(k+1)$ individually carry a parasitic $\log(k+1)$; the combination $t-t^3$ cancels it exactly, because $(\gamma+\log 2)/2-(\gamma+\log 4)/4=\gamma/4$. The cancellation is forced: writing $\log(k+1)=\sum_p v_p(k+1)\log p$ and using the $\mathbb Q$-linear independence of $\{\log p\}$, the vanishing of the parasite for coefficients supported on $k\le 3$ requires the $k=2$ coefficient to vanish (prime $3$) and the $k=1,3$ coefficients to be opposite (prime $2$).
-- source:
--   Derived from int_0^infty e^{-au} log u du = -(gamma + log a)/a (Gradshteyn-Ryzhik 4.331.1) at a = 2 and a = 4.

import Mathlib
open MeasureTheory

theorem EulerMascheroni.LogPower.gamma_quarter :
    ∫ u in Set.Ioi (0:ℝ), (Real.exp (-2 * u) - Real.exp (-4 * u)) * (-Real.log u)
      = Real.eulerMascheroniConstant / 4 := by
  sorry
