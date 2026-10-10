-- Prove2me | Theorems.Thm_ConleyZehnder_exists_rotation_mul_mem_spStar
-- name    : ConleyZehnder.exists_rotation_mul_mem_spStar
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:46:02.95098+00:00
-- url     : https://prove2.me/theorems/4c1d4759-0e27-444c-baa6-c8dde0ab8436
-- title:
--   Every symplectic matrix is rotated into Sp* by some unitary rotation
-- statement:
--   Let $J_0=\begin{pmatrix}0&-\mathrm{Id}\ \mathrm{Id}&0\end{pmatrix}$, let $\mathrm{Sp}(2n)=\{A: AJ_0A^T=J_0\}$, and for $\theta\in\mathbb R$ let $e^{\theta J_0}=\cos\theta\,\mathrm{Id}+\sin\theta\,J_0$ be the rotation by $\theta$ in every complex coordinate plane. For every $A\in\mathrm{Sp}(2n)$ there is $\theta\in\mathbb R$ with
--   $$\det\bigl(\mathrm{Id}-A\,e^{\theta J_0}\bigr)\neq 0,$$
--   i.e. $A\,e^{\theta J_0}\in\mathrm{Sp}^*(2n)$, the symplectic matrices without eigenvalue $1$.
--
--   So every symplectic matrix is moved into $\mathrm{Sp}^*(2n)$ by a suitable unitary rotation. This lets facts about $\mathrm{Sp}^*(2n)$ (for instance that each of its points is joined inside $\mathrm{Sp}^*$ to $W^+$ or $W^-$) be transferred to all of $\mathrm{Sp}(2n)$.
--
--   Formalization note: `SpStar n` (definition module `ConleyZehnder_Setting`) is the set of symplectic `A` with `(1 - A).det ≠ 0`; `J₀ n` is Mathlib's `Matrix.J`. The product $A\,e^{\theta J_0}$ is symplectic automatically, so the content is the determinant condition.
-- source:
--   Used in the classical proof that Sp(2n) is connected; cf. Classical; see McDuff-Salamon, Introduction to Symplectic Topology, 3rd ed., Section 2.2; used in Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (1)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- For every symplectic matrix `A` there is an angle `θ` such that `A · e^{θ J₀}`, with
`e^{θ J₀} = cos θ · Id + sin θ · J₀`, does not have `1` as an eigenvalue. -/
theorem exists_rotation_mul_mem_spStar {n : ℕ} (A : Mat n) (hA : IsSymplectic A) :
    ∃ θ : ℝ, A * (Real.cos θ • (1 : Mat n) + Real.sin θ • J₀ n) ∈ SpStar n := by sorry

end ConleyZehnder
