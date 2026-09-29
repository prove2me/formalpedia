-- Prove2me | Theorems.Thm_CuspForm_heckeTLin_apply_eq_smul_iff
-- name    : CuspForm.heckeTLin_apply_eq_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/5d086b7a-70ef-5a66-acdd-3a4fb12e10ea
-- title:
--   Eigenform criterion for Tₚ in terms of q-coefficients
-- statement:
--   Let $N$ be a natural number, $k$ an integer and $p$ a prime with $p \nmid N$; let $f$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(N)$, and let $c \in \mathbb{C}$. The assertion is an equivalence. On one side stands the equation $T_p f = c \cdot f$ inside the complex vector space of cusp forms of weight $k$ for $\Gamma_0(N)$, where $T_p$ is the $\mathbb{C}$-linear endomorphism [`CuspForm.heckeTLin k hp hpN`](def/ModularForm_HeckeOperatorForms.html#L69) whose value at $f$ has underlying function [`ModularForm.heckeT k p`](def/ModularForm_HeckeOperator.html#L96) applied to $f$, namely $U_p f + f \mid_k \bigl(\mathrm{heckeDiagMatrix}\ p\bigr)$, and where $c \cdot f$ is the scalar multiple in that space. On the other side stands a condition on the coefficients $a_n :=$ [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $f$ of width $1$: for every natural number $n$ (including $n = 0$),
--   $$a_{np} + \begin{cases} p^{k-1} a_{n/p}, & p \mid n,\\ 0, & p \nmid n,\end{cases} \;=\; c\, a_n,$$
--   this left-hand side being [`ModularForm.coeffHeckeT k p (qCoeff f) n`](def/ModularForm_HeckeOperator.html#L162).
--
--   This is the standard criterion identifying $T_p$-eigenforms in $S_k(\Gamma_0(N))$, for $p$ prime to the level, by the Hecke recursion $a_{np} + p^{k-1}a_{n/p} = c\,a_n$ among the $q$-expansion coefficients. It is the form in which the eigenvalue condition is used when producing normalised eigenforms and when analysing the action of the Hecke algebra on spaces of cusp forms, and it is cited in the construction of normalised eigenforms with prescribed coefficients and in the newform arguments that follow.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeTLin_apply_eq_smul_iff.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.heckeTLin_apply_eq_smul_iff {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeTLin k hp hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by sorry
