-- Prove2me | Theorems.Thm_DualAssembly_sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree
-- name    : DualAssembly.sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/6c44ff6d-7db7-5fd1-9ab5-e31843e12b59
-- title:
--   Joint eigenvalues never satisfy a² = c² e
-- statement:
--   Let $p$ be a prime and let $T$ be a $\mathbb{Z}_p$-module (an additive commutative group with a $\mathbb{Z}_p$-module structure, with no finiteness or freeness assumed), and let $K$ be an algebraically closed field of characteristic zero equipped with a $\mathbb{Z}_p$-algebra structure. Let $A$ and $D$ be $\mathbb{Z}_p$-linear endomorphisms of $T$, let $m$ be a natural number with $m > 0$ and suppose $D^m = 1$. Let $c$ be a natural number and $P \in \mathbb{Z}[X]$ a monic polynomial with $P(A) = 0$ (as an element of the $\mathbb{Z}$-algebra of endomorphisms) and such that every complex number $z$ with $P(z) = 0$ satisfies $\lVert z\rVert < c$. Suppose finally that $v \in K \otimes_{\mathbb{Z}_p} T$ is non-zero and is a joint eigenvector of the base-changed operators: $A_K v = a\, v$ and $D_K v = e\, v$ for scalars $a, e \in K$. Then $a^2 \neq \iota(c)^2 \, e$, where $\iota(c)$ denotes the image in $K$ of the natural number $c$ viewed in $\mathbb{Z}_p$ under the structure map $\mathbb{Z}_p \to K$.
--
--   This is the elementary algebraic separation step that converts an archimedean bound on the roots of the characteristic-type polynomial annihilating a Hecke-style operator, together with the finite order of a diamond operator, into the non-vanishing of $a^2 - c^2 e$ on joint eigenvectors; the hypotheses are arranged so that $T$ may be an arbitrary $\mathbb{Z}_p$-module, in particular a Tate module of a Jacobian. It is applied in [`ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia`](thm.html#ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia), with $c = p+1$ and the Weil bound supplying the root estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DualAssembly_sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem DualAssembly.sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree
    (p : ℕ) [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Algebra ℤ_[p] K]
    (A D : Module.End ℤ_[p] T) (m : ℕ) (hm : 0 < m) (hD : D ^ m = 1)
    (c : ℕ) (P : Polynomial ℤ) (hPm : P.Monic) (hPA : Polynomial.aeval A P = 0)
    (hroots : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ < c)
    (v : K ⊗[ℤ_[p]] T) (a e : K) (hv : v ≠ 0)
    (hA : A.baseChange K v = a • v) (hDv : D.baseChange K v = e • v) :
    a ^ 2 ≠ (algebraMap ℤ_[p] K ((c : ℕ) : ℤ_[p])) ^ 2 * e := by sorry
