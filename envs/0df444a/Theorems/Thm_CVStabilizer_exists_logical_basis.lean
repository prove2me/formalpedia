-- Prove2me | Theorems.Thm_CVStabilizer_exists_logical_basis
-- name    : CVStabilizer.exists_logical_basis
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:20.836394+00:00
-- url     : https://prove2.me/theorems/46f90ab8-56cd-4916-98f7-729495a540df
-- title:
--   A symplectic basis $x_1,z_1,\dots,x_{n-k},z_{n-k}$ of $W^\omega/W$
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb R^{2n}$ be linearly independent with $\omega(u_i,u_j)=0$ for all $i,j$, and $W=\operatorname{span}\{u_i\}$. There exist vectors $x_1,z_1,\dots,x_{n-k},z_{n-k}\in W^\omega$ such that
--
--   $$
--   \omega(x_i,x_j)=\omega(z_i,z_j)=0,\qquad \omega(x_i,z_j)=\delta_{ij}\quad(1\le i,j\le n-k),
--   $$
--
--   and whose classes form a basis of $W^\omega/W$: the family $u_1,\dots,u_k,x_1,\dots,x_{n-k},z_1,\dots,z_{n-k}$ is linearly independent and spans $W^\omega$.
--
--   These are the logical position and momentum directions of the code.
--
--   Differences from the source:
--   - reading: k vectors u₁, …, u_k with ω(uᵢ, uⱼ) = 0, and dim W = k used in 'dim W^ω = dim ℝ²ⁿ − dim W = 2n − k' → LinearIndependent ℝ u; reason: the page uses dim W = k; without independence the claim fails (n = 1, k = 2, u₁ = u₂ = (1, 0): dim W^ω = 1 ≠ 0)
--   - encoding: W^ω = {v : ω(v, uᵢ) = 0 ∀i} → (omega n).orthogonal W = {v | ∀ w ∈ W, ω(w, v) = 0}; reason: equal sets, by antisymmetry and linearity of ω
--   - encoding: n − k logical modes, 2n − k, 2(n − k) → k ≤ n is concluded; natural-number subtraction and index type Fin (n − k); reason: since k ≤ n is proved, the subtractions are the true differences
--   - encoding: a basis x₁, z₁, …, x_{n−k}, z_{n−k} ∈ ℝ²ⁿ for W^ω/W → xᵢ, zᵢ ∈ W^ω and the joint family (u, x, z) is linearly independent and spans W^ω; reason: equivalent to the classes of the xᵢ, zᵢ forming a basis of W^ω/W, without quotient types
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, p.2, left column ("Now we can construct a basis x1, z1, . . . , xn−k, zn−k ∈R2n for W ω/W such that ω(xi, xj) = ω(zi, zj) = 0 and ω(xi, zj) = δij")

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **A symplectic basis of `W^ω/W`**, Barnes, arXiv:quant-ph/0405064v1, p.2: "Now we can
construct a basis x₁, z₁, . . . , x_{n−k}, z_{n−k} ∈ ℝ²ⁿ for W^ω/W such that
ω(xᵢ, xⱼ) = ω(zᵢ, zⱼ) = 0 and ω(xᵢ, zⱼ) = δᵢⱼ." For linearly independent `u₁, …, u_k` with
`ω(uᵢ, uⱼ) = 0` there are `x₁, z₁, …, x_{n−k}, z_{n−k} ∈ W^ω` with these relations whose classes
form a basis of `W^ω/W`.

**Formalization Note** "The classes of `xᵢ, zᵢ` form a basis of `W^ω/W`" is stated as: the joint
family `(u₁, …, u_k, x₁, …, x_{n−k}, z₁, …, z_{n−k})` is linearly independent and spans `W^ω`,
which is equivalent and avoids quotient types. The index range `Fin (n − k)` is honest because
`k ≤ n` (`finrank_orthogonal`). -/
theorem exists_logical_basis (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hu : LinearIndependent ℝ u) (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    let W : Submodule ℝ (PhaseSpace n) := Submodule.span ℝ (Set.range u)
    let Wω : Submodule ℝ (PhaseSpace n) := (omega n).orthogonal W
    ∃ x z : Fin (n - k) → PhaseSpace n,
      (∀ i, x i ∈ Wω ∧ z i ∈ Wω) ∧
      (∀ i j, omega n (x i) (x j) = 0 ∧ omega n (z i) (z j) = 0 ∧
        omega n (x i) (z j) = if i = j then 1 else 0) ∧
      LinearIndependent ℝ (Sum.elim u (Sum.elim x z)) ∧
      Submodule.span ℝ (Set.range (Sum.elim u (Sum.elim x z))) = Wω := by sorry

end CVStabilizer
