-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_fract_eq_scaled_integral_of_rat
-- name    : EulerMascheroni.Sondow.fract_eq_scaled_integral_of_rat
-- status  : Open
-- author  : @shivm
-- created : 2026-10-09T09:40:37.18753+00:00
-- url     : https://prove2.me/theorems/1bb2f3a3-d459-4dc9-b742-b45ab64f8753
-- title:
--   If $\gamma$ is rational then $\{d_{2n}L_n\}=d_{2n}I_n$ for all large $n$
-- statement:
--   Assume Euler's constant is rational, say $\gamma=p/q$ in lowest terms. Then for all sufficiently large $n$,
--   $$\{d_{2n}L_n\}=d_{2n}I_n,$$
--   where $d_{2n}=\operatorname{lcm}(1,\dots,2n)$, and $L_n$, $I_n$, $A_n$ are Sondow's quantities.
--
--   **Role.** This is the exact arithmetic core of Sondow's Corollary 6. Multiplying the proved identity $I_n=\binom{2n}{n}\gamma+L_n-A_n$ by $d_{2n}$ gives
--   $$d_{2n}L_n=d_{2n}A_n-q_n\gamma+d_{2n}I_n,\qquad q_n:=d_{2n}\binom{2n}{n}\in\mathbb Z,$$
--   and $d_{2n}A_n\in\mathbb Z$ is already proved. Once $2n\ge q$ we have $q\mid d_{2n}$, hence $q_n\gamma\in\mathbb Z$, so $d_{2n}L_n$ differs from $d_{2n}I_n$ by an integer; combined with the proved bound $0<d_{2n}I_n<2^{-n}$ for large $n$ this pins the fractional part exactly.
--
--   Together with that bound it yields $\{d_{2n}L_n\}<2^{-n}$ for all large $n$ whenever $\gamma\in\mathbb Q$, which is the contrapositive of Sondow's criterion. It also makes precise what the open hypothesis `fractional_lower_bound_conjecture` is asking: that hypothesis fails exactly when $\operatorname{dist}(q_n\gamma,\mathbb Z)<2^{1-n}$ for every large $n$, i.e. when $|\gamma-m_n/q_n|<q_n^{-1-\varepsilon}$ with $\varepsilon=\log 2/\log(4e^2)\approx0.205$ along the prescribed sequence $q_n$, since $\log q_n\sim n(2+\log 4)$. That is a Liouville-type non-approximability condition on a fixed sparse denominator sequence, so the open hypothesis is irrationality together with a further quantitative statement, not a weakening of it.
-- source:
--   Jonathan Sondow, Criteria for Irrationality of Euler's Constant, https://arxiv.org/pdf/math/0209070 (v2, 2002), eq. (2),(6),(8) and Corollary 6; arithmetic core of that corollary.

import Mathlib
import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.fract_eq_scaled_integral_of_rat
    (hq : ∃ r : ℚ, Real.eulerMascheroniConstant = (r : ℝ)) :
    ∀ᶠ n in Filter.atTop, Int.fract ((d (2*n) : ℝ) * L n) = (d (2*n) : ℝ) * I n := by
  sorry
