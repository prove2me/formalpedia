-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_symplectic_transport
-- name    : CauchyRiemannIndex.exists_symplectic_transport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:22.508344+00:00
-- url     : https://prove2.me/theorems/e7f1ad6c-fec2-478b-ab4e-55d1449c19fb
-- title:
--   A continuous local transport of nonzero vectors by symplectic matrices
-- statement:
--   For every $n$ there are an open set $U\subseteq\mathbb R^{2n}\times\mathbb R^{2n}$ containing all pairs $(u,u)$ with $u\neq0$ and a map $\tau:U\to\mathrm{Sp}(2n,\mathbb R)$, continuous on $U$, such that for all $(u,v)\in U$
--   $$\tau(u,v)\,u=v,\qquad\text{and}\qquad \tau(u,u)=\mathrm{Id}\ \text{ whenever }(u,u)\in U .$$
--
--   In other words, the orbit map $A\mapsto Au$ of $\mathrm{Sp}(2n,\mathbb R)$ on $\mathbb R^{2n}\setminus\{0\}$ admits a continuous local section near the diagonal, normalised to be the identity on the diagonal.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`, first block $q$, second block $p$) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`. Vectors of $\mathbb R^{2n}$ are functions `Fin n ⊕ Fin n → ℝ` and $Av$ is `A *ᵥ v`. `τ` is a total function on pairs `(Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → ℝ)`, and its continuity, symplecticity and the two identities are required only on `U` (`ContinuousOn τ U`).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (Theorem 3.34 and the Maslov index of loops in $\mathrm{Sp}(2n)$); J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2 (the map $\hat\rho$, eq. (9))

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- Near the diagonal of `(ℝ²ⁿ ∖ {0})²` there is a continuous choice `τ(u, v)` of a symplectic
matrix sending `u` to `v`, with `τ(u, u) = Id`. -/
theorem exists_symplectic_transport (n : ℕ) :
    ∃ U : Set ((Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → ℝ)), IsOpen U ∧
      (∀ u, u ≠ 0 → (u, u) ∈ U) ∧
      ∃ τ : (Fin n ⊕ Fin n → ℝ) × (Fin n ⊕ Fin n → ℝ) → Mat n, ContinuousOn τ U ∧
        ∀ p ∈ U, IsSymplectic (τ p) ∧ τ p *ᵥ p.1 = p.2 ∧ (p.1 = p.2 → τ p = 1) := by sorry

end CauchyRiemannIndex
