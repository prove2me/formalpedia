-- Prove2me | Theorems.Thm_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime
-- name    : CuspForm.exists_gamma1_qCoeff_eq_ite_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/4397c499-4ee0-5dbe-839c-c4f2073e0a03
-- title:
--   Depletion of a Γ₁(N) cusp form away from Q
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ (imposed as a `NeZero` instance), let $k$ be an integer, and let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_1(N)$. Let $Q$ be a natural number with $Q \neq 0$, and let $M$ be a natural number divisible by $N Q^2$. The assertion is that there exists a cusp form $g$ of weight $k$ for $\Gamma_1(M)$ such that for every natural number $n$ the $n$-th coefficient of the $q$-expansion of $g$ equals the $n$-th coefficient of the $q$-expansion of $f$ when $n$ and $Q$ are coprime, and equals $0$ otherwise. Here the $q$-expansion coefficients are those given by [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19), namely `qCoeff h n` is the $n$-th coefficient of the width-one $q$-expansion `qExpansion 1 h` of the function $h : \mathbb{H} \to \mathbb{C}$, i.e. the expansion in $q = e^{2\pi i \tau}$ at the cusp $\infty$; both $f$ and $g$ are used via their underlying functions on the upper half-plane. Coprimality is `Nat.Coprime`, i.e. $\gcd(n, Q) = 1$ (so $n = 0$ contributes only when $Q = 1$).
--
--   This is the classical depletion of $f$ away from $Q$, that is, the twist of $f$ by the principal Dirichlet character modulo $Q$, which lives on level $N Q^2$ and hence on any level divisible by it. It feeds the vanishing statement [`CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero`](thm.html#CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero) and the constructions of Galois representations attached to weight-one eigenforms in the Deligne–Serre and Langlands–Tunnell parts of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem CuspForm.exists_gamma1_qCoeff_eq_ite_coprime (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (Gamma1 N) k) (Q : ℕ) (hQ : Q ≠ 0) (M : ℕ) (hM : N * Q ^ 2 ∣ M) :
    ∃ g : CuspForm (Gamma1 M) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime Q then ModularFormClass.qCoeff f n else 0 := by sorry
