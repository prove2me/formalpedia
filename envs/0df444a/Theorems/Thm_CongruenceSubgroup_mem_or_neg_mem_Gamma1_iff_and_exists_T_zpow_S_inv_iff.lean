-- Prove2me | Theorems.Thm_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff
-- name    : CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9c3d5976-9f9c-596a-a22e-cb8843e7394c
-- title:
--   First-column criteria for ±Γ₁(N)-membership
-- statement:
--   Let $N$ be a natural number, with no positivity assumed (so $N=0$, where $\mathbb{Z}/N\mathbb{Z}=\mathbb{Z}$, is allowed), and let $\beta\in\mathrm{SL}_2(\mathbb{Z})$, with entries $a=\beta_{00}$, $b=\beta_{01}$, $c=\beta_{10}$, $d=\beta_{11}$. Here $\Gamma_1(N)$ is Mathlib's congruence subgroup, membership in which amounts to $\gamma_{00}\equiv\gamma_{11}\equiv 1$ and $\gamma_{10}\equiv 0$ in $\mathbb{Z}/N\mathbb{Z}$, and $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ are the standard elements of the modular group. The assertion is the conjunction of three statements about the reductions of the first column modulo $N$. First, $\beta\in\Gamma_1(N)$ or $-\beta\in\Gamma_1(N)$ holds if and only if $\bar c=0$ and $\bar a\in\{1,-1\}$. Second, there exists $j\in\mathbb{Z}$ with $\beta T^{j}S^{-1}\in\Gamma_1(N)$ or $-(\beta T^{j}S^{-1})\in\Gamma_1(N)$ if and only if $\bar c\in\{1,-1\}$. Third, there exist $\alpha,\beta'\in\mathbb{Z}/N\mathbb{Z}$ with $\alpha\bar a+\beta'\bar c=1$, i.e. the reduced first column is unimodular modulo $N$.
--
--   The first two equivalences are the standard criteria for $\beta\infty$ to be the cusp $\infty$, respectively the cusp $0=S\infty$, of $\Gamma_1(N)$, read off from the first column of $\beta$ modulo $N$ up to sign; the third records that this column is primitive modulo $N$. The statement is used in the construction of auxiliary $\Gamma_1(N)$-forms with prescribed behaviour at the cusps, in [`ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd`](thm.html#ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups in

theorem CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff
    (N : ℕ) (β : SL(2, ℤ)) :
    ((β ∈ CongruenceSubgroup.Gamma1 N ∨ -β ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 0 ∧
          (((β 0 0 : ℤ) : ZMod N) = 1 ∨ ((β 0 0 : ℤ) : ZMod N) = -1))) ∧
    ((∃ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∈ CongruenceSubgroup.Gamma1 N ∨
        -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∈ CongruenceSubgroup.Gamma1 N) ↔
        (((β 1 0 : ℤ) : ZMod N) = 1 ∨ ((β 1 0 : ℤ) : ZMod N) = -1)) ∧
    (∃ a b : ZMod N, a * ((β 0 0 : ℤ) : ZMod N) + b * ((β 1 0 : ℤ) : ZMod N) = 1) := by sorry
