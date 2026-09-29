-- Prove2me | Theorems.Thm_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime
-- name    : CuspForm.exists_qCoeff_eq_ite_dvd_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/24769243-59bf-549f-8b9a-38bb5c276a9b
-- title:
--   p-depletion of a cusp form on Γ₁(N)
-- statement:
--   Let $N$ be a natural number that is nonzero, let $k$ be an integer, let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(N)$, and let $p$ be a prime number. The assertion is that there exists a cusp form $g$ of weight $k$ for $\Gamma_1(p^2N)$ such that for every natural number $n$ the $n$-th coefficient of the $q$-expansion of $g$ at width $1$, that is the coefficient of $X^n$ in `qExpansion 1` of $g$, equals $0$ when $p \mid n$ and equals the corresponding coefficient of the $q$-expansion of $f$ at width $1$ when $p \nmid n$. Here both $f$ and $g$ are regarded as functions on the upper half-plane, and [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) is the coefficient extracted from the width-$1$ $q$-expansion, so the conclusion is the coefficientwise identity $a_n(g) = a_n(f)$ for $n$ prime to $p$ and $a_n(g) = 0$ for $n$ divisible by $p$ (in particular $a_0(g) = 0$). No relation between $p$ and $N$ is assumed.
--
--   This is the passage from $f = \sum a_n q^n$ to its $p$-depletion $\sum_{p \nmid n} a_n q^n$, classically realised as $f - (f \mid U_p) \mid V_p$, equivalently as the twist of $f$ by the trivial character modulo $p$, at the cost of raising the level from $N$ to $p^2 N$. It is used in the Langlands–Tunnell part of the argument, where the construction of a weight-one form with prescribed behaviour removes the coefficients at multiples of the wild prime $p = 3$ while making the level divisible by $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_qCoeff_eq_ite_dvd_of_prime
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (p : ℕ) (hp : p.Prime) :
    ∃ g : CuspForm (Gamma1 (p ^ 2 * N)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n = if p ∣ n then 0 else ModularFormClass.qCoeff f n := by sorry
