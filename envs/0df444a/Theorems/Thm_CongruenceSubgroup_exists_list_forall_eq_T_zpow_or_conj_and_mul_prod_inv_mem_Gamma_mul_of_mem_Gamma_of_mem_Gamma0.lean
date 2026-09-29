-- Prove2me | Theorems.Thm_CongruenceSubgroup_exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0
-- name    : CongruenceSubgroup.exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/df5f707a-4aca-57a2-93a0-7f4575965536
-- title:
--   Generation of Γ(q)∩Γ₀(M') modulo Γ(qℓ)
-- statement:
--   Let $q$ and $\ell$ be primes with $\ell \neq q$, and let $M' \geq 1$ be an integer not divisible by $\ell$. The conclusion is a conjunction of two assertions about $SL(2,\mathbb{Z})$. First, there exists $w \in SL(2,\mathbb{Z})$ lying in the principal congruence subgroup $\Gamma(q)$ and in $\Gamma_0(M')$ whose entries satisfy $w_{00} \equiv 0$, $w_{01} \equiv -1$, $w_{10} \equiv 1$ and $w_{11} \equiv 0$ in $\mathbb{Z}/\ell$, i.e. $w$ is congruent modulo $\ell$ to $\begin{pmatrix} 0 & -1 \\ 1 & 0\end{pmatrix}$. Second, for every $w \in \Gamma(q) \cap \Gamma_0(M')$ satisfying those four congruences modulo $\ell$, and for every $\gamma \in \Gamma(q) \cap \Gamma_0(M')$, there is a finite list $l$ of elements of $SL(2,\mathbb{Z})$ such that each entry $e$ of $l$ is of the form $e = T^{s}$ or $e = w T^{s} w^{-1}$ for some integer $s$ divisible by $q$, where $T = \begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$, and such that the product $p$ of $l$ (in order) satisfies $\gamma p^{-1} \in \Gamma(q\ell)$ and $p \in \Gamma_0(M')$.
--
--   This is the elementary-matrix generation statement for $SL_2(\mathbb{F}_\ell)$ transported to $\Gamma(q) \cap \Gamma_0(M')$: modulo $\Gamma(q\ell)$, every element of $\Gamma(q) \cap \Gamma_0(M')$ is a product of upper unipotents $T^{s}$ with $q \mid s$ and of their conjugates by a single fixed element $w$ reducing to the Weyl element modulo $\ell$; the first half is a Chinese remainder statement for $SL_2$, proved from the simultaneous realisation of prescribed reductions at coprime moduli. It is used in the study of level automorphisms of modular curves, where it reduces a condition on all of $\Gamma(q) \cap \Gamma_0(M')$ to a condition on the listed generators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CongruenceSubgroup_exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (M' : ℕ) [NeZero M'] (hℓM' : ¬ ℓ ∣ M') :

    (∃ w : SL(2, ℤ), w ∈ CongruenceSubgroup.Gamma q ∧ w ∈ CongruenceSubgroup.Gamma0 M' ∧
      ((w 0 0 : ℤ) : ZMod ℓ) = 0 ∧ ((w 0 1 : ℤ) : ZMod ℓ) = -1 ∧
      ((w 1 0 : ℤ) : ZMod ℓ) = 1 ∧ ((w 1 1 : ℤ) : ZMod ℓ) = 0) ∧

    (∀ w : SL(2, ℤ), w ∈ CongruenceSubgroup.Gamma q → w ∈ CongruenceSubgroup.Gamma0 M' →
      ((w 0 0 : ℤ) : ZMod ℓ) = 0 → ((w 0 1 : ℤ) : ZMod ℓ) = -1 →
      ((w 1 0 : ℤ) : ZMod ℓ) = 1 → ((w 1 1 : ℤ) : ZMod ℓ) = 0 →
      ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∃ l : List (SL(2, ℤ)),
          (∀ e ∈ l, ∃ s : ℤ, (q : ℤ) ∣ s ∧ (e = ModularGroup.T ^ s ∨ e = w * ModularGroup.T ^ s * w⁻¹)) ∧
          γ * (l.prod)⁻¹ ∈ CongruenceSubgroup.Gamma (q * ℓ) ∧
          l.prod ∈ CongruenceSubgroup.Gamma0 M') := by sorry
