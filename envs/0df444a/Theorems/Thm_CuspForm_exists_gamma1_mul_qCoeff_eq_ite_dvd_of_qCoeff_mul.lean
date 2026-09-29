-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul
-- name    : CuspForm.exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/b00bab02-fa02-5f1c-bb44-bc8a3afe012d
-- title:
--   Depletion at q of a U_q-multiplicative cusp form
-- statement:
--   Let $N$ be a nonzero natural number, $k$ an integer, and $f$ a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(N)$; let $q$ be a nonzero natural number. Write $a_n(h) :=$ [`ModularFormClass.qCoeff h n`](def/FLTPrelim_Modularity.html#L19) for the $n$-th coefficient of the $q$-expansion of $h$ taken with respect to the period $1$, i.e. the coefficient of index $n$ in `qExpansion 1 h`. Assume that the expansion of $f$ is multiplicative at $q$ in the sense that for every natural number $n$ one has $a_{qn}(f) = a_q(f)\,a_n(f)$ (the case $n = 0$ is included). The conclusion is that there exists a cusp form $g$ of the same weight $k$ for $\Gamma_1(Nq)$ whose expansion coefficients are obtained from those of $f$ by deleting the indices divisible by $q$: for every natural number $n$, $a_n(g) = 0$ if $q \mid n$, and $a_n(g) = a_n(f)$ otherwise.
--
--   This is the classical $q$-depletion $g = f - a_q(f)\,(f\mid V_q)$ of a cusp form whose coefficients satisfy $a_{qn} = a_q a_n$, the point being that the level is raised by a single factor of $q$ rather than by $q^2$. It is used in the Langlands–Tunnell part of the argument, in the construction of a weight-one form realising a given character situation with prescribed non-divisibility of the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (q : ℕ) (hq : q ≠ 0)
    (hfU : ∀ n : ℕ, ModularFormClass.qCoeff f (q * n) =
      ModularFormClass.qCoeff f q * ModularFormClass.qCoeff f n) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 (N * q)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if q ∣ n then 0 else ModularFormClass.qCoeff f n := by sorry
