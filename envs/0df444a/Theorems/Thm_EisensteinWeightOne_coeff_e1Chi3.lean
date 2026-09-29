-- Prove2me | Theorems.Thm_EisensteinWeightOne_coeff_e1Chi3
-- name    : EisensteinWeightOne.coeff_e1Chi3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/24fb5486-cbbd-5a49-bf32-427a2f5a3e17
-- title:
--   Coefficients of the power series e₁(χ₋₃)
-- statement:
--   Let $\chi_{-3} : \mathbb{N} \to \mathbb{Z}$ be the function `chiNegThree` given by $\chi_{-3}(n) = 1$ if $n \equiv 1 \pmod 3$, $\chi_{-3}(n) = -1$ if $n \equiv 2 \pmod 3$, and $\chi_{-3}(n) = 0$ otherwise, and let $\sigma_{\chi}(n) = \sum_{d \mid n} \chi_{-3}(d)$ be the twisted divisor sum `sigmaChi`, the sum over the divisors of $n$ in the sense of `Nat.divisors` (so $\sigma_\chi(0) = 0$, the divisor set of $0$ being empty). The integral formal power series `e1Chi3` is defined as the series whose $n$-th coefficient is $1$ for $n = 0$ and $6\,\sigma_\chi(n)$ for $n \neq 0$. The assertion is that for every natural number $n$, the $n$-th coefficient of `e1Chi3`, taken in the sense of `PowerSeries.coeff`, equals $1$ if $n = 0$ and $6\,\sigma_\chi(n)$ otherwise. Thus the statement records that the coefficient extraction applied to `e1Chi3` returns exactly the defining coefficient function; no modularity or convergence property is asserted here.
--
--   The series `e1Chi3` plays the role of the $q$-expansion of the weight-one Eisenstein series $E_1(1,\chi_{-3})$ on $\Gamma_1(3)$, whose constant term $1$ and coefficients divisible by $6$ give the congruence $E_1(1,\chi_{-3}) \equiv 1 \pmod 3$ used to pass from weight one to weight two in the Langlands–Tunnell step. It is cited by [`CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd`](thm.html#CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinWeightOne_coeff_e1Chi3.lean

import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open EisensteinWeightOne

theorem EisensteinWeightOne.coeff_e1Chi3 (n : ℕ) :
  (PowerSeries.coeff n) EisensteinWeightOne.e1Chi3 = if n = 0 then 1 else 6 * EisensteinWeightOne.sigmaChi n := by sorry
