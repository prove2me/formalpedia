-- Prove2me | Theorems.Thm_CauchyRiemannIndex_diagonal_isSymplectic
-- name    : CauchyRiemannIndex.diagonal_isSymplectic
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T17:31:44.452867+00:00
-- url     : https://prove2.me/theorems/dcfdfad4-73c6-48f7-99e3-c0f7b407c016
-- title:
--   Diagonal matrices with reciprocal $q_k$, $p_k$ entries are symplectic
-- statement:
--   Let $d_1,\dots,d_{2n}$ be real numbers indexed by the coordinates $q_1,\dots,q_n,p_1,\dots,p_n$ of $\mathbb R^{2n}$, and suppose
--   $$d_{q_k}\,d_{p_k}=1\qquad(k=1,\dots,n).$$
--   Then the diagonal matrix $D=\mathrm{diag}(d)$ is symplectic: $DJ_0D^T=J_0$, i.e. $D\in\mathrm{Sp}(2n,\mathbb R)$.
--
--   These diagonal matrices form the standard maximal torus of $\mathrm{Sp}(2n,\mathbb R)$ (independent scalings $q_k\mapsto\lambda_kq_k$, $p_k\mapsto\lambda_k^{-1}p_k$), a basic family of explicit symplectic matrices.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`, first block $q$, second block $p$) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`, i.e. $AJ_0A^T=J_0$. The diagonal entries are a function `d : Fin n ⊕ Fin n → ℝ`, with $d_{q_k}$ = `d (Sum.inl k)` and $d_{p_k}$ = `d (Sum.inr k)`, and $D$ is `Matrix.diagonal d`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (Theorem 3.34 and the Maslov index of loops in $\mathrm{Sp}(2n)$); J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- A diagonal matrix `diag(d)` on `ℝ²ⁿ` whose entries at `q_k` and `p_k` multiply to `1` for
every `k` is symplectic. -/
theorem diagonal_isSymplectic {n : ℕ} (d : Fin n ⊕ Fin n → ℝ)
    (hd : ∀ k, d (Sum.inl k) * d (Sum.inr k) = 1) : IsSymplectic (Matrix.diagonal d) := by sorry

end CauchyRiemannIndex
