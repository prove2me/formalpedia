-- Prove2me | Theorems.Thm_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
-- name    : CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/bb5eb3f6-6a96-5533-a4d4-4e8028c12a22
-- title:
--   Coefficients prime to K vanish implies coefficients prime to N vanish
-- statement:
--   Let $N$ be a non-zero natural number, $k$ an integer, and $K$ a non-zero natural number. Let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(N)$, and write $a_m =$ [`ModularFormClass.qCoeff f m`](def/FLTPrelim_Modularity.html#L19) for the $m$-th coefficient of the $q$-expansion of width $1$ of the underlying function $\mathbb{H} \to \mathbb{C}$, i.e. the $m$-th coefficient of `qExpansion 1 f`. Assume that $a_m = 0$ for every natural number $m$ coprime to $K$. Then for every natural number $n$ coprime to $N$ one has $a_n = 0$. In other words, the vanishing of the coefficients at indices prime to an arbitrary non-zero modulus $K$ forces the vanishing of the coefficients at all indices prime to the level $N$ itself; the primes dividing $K$ but not $N$ impose no genuine restriction.
--
--   This is the first step of Atkin and Lehner's analysis of forms with many vanishing Fourier coefficients, stated as part (i) of Li's Theorem 1. It is used in the project to pass from a condition of coprimality to an auxiliary modulus to one of coprimality to the level, and is cited by [`CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`](thm.html#CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0)
    (n : ℕ) (hn : Nat.Coprime n N) : ModularFormClass.qCoeff f n = 0 := by sorry
