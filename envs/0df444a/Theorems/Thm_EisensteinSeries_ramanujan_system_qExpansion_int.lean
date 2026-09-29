-- Prove2me | Theorems.Thm_EisensteinSeries_ramanujan_system_qExpansion_int
-- name    : EisensteinSeries.ramanujan_system_qExpansion_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/662f1fa5-3d57-5d53-999d-fe1beaf7f749
-- title:
--   Ramanujan's differential system for P, Q, R
-- statement:
--   Let $P$, $Q$, $R$ be formal power series with integer coefficients, and suppose each is pinned down coefficientwise: the coefficient of $P$ in degree $0$ is $1$ and in degree $n \ge 1$ is $-24\sum_{d \mid n} d$; the coefficient of $Q$ in degree $0$ is $1$ and in degree $n \ge 1$ is $240\sum_{d \mid n} d^{3}$; the coefficient of $R$ in degree $0$ is $1$ and in degree $n \ge 1$ is $-504\sum_{d \mid n} d^{5}$ (the sums being over the divisor finset of $n$, so over the positive divisors). Thus $P$, $Q$, $R$ are the integral $q$-expansions of $E_2$, $E_4$, $E_6$. Writing $\theta F$ for `PowerSeries.X * PowerSeries.derivative ℤ F`, i.e. $q\,dF/dq$ formed with the formal derivative on $\mathbb{Z}[[q]]$, the conclusion is the conjunction of the three identities $12\,\theta P = P^{2} - Q$, $3\,\theta Q = PQ - R$ and $2\,\theta R = PR - Q^{2}$, as equalities in $\mathbb{Z}[[q]]$ (the integer factors $12$, $3$, $2$ acting as the corresponding constant power series).
--
--   These are Ramanujan's differential equations for the Eisenstein series $E_2$, $E_4$, $E_6$, stated purely formally as identities between integral $q$-series. They are used in this development for computations with the theta operator on $q$-expansions of level-one modular forms, entering the treatment of $j$-expansions on the modular curve and the congruence constraint on the weight of a level-one form whose $q$-expansion is congruent to a constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinSeries_ramanujan_system_qExpansion_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem EisensteinSeries.ramanujan_system_qExpansion_int
    (P Q R : PowerSeries ℤ)
    (hP : P = PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ))
    (hQ : Q = PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3)
    (hR : R = PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) :
    12 * (PowerSeries.X * PowerSeries.derivative ℤ P) = P ^ 2 - Q ∧
      3 * (PowerSeries.X * PowerSeries.derivative ℤ Q) = P * Q - R ∧
        2 * (PowerSeries.X * PowerSeries.derivative ℤ R) = P * R - Q ^ 2 := by sorry
