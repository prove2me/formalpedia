-- Prove2me | Theorems.Thm_CongruencyTU_theorem_19
-- name    : CongruencyTU.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:03.797104+00:00
-- url     : https://prove2.me/theorems/1a043d11-c7b0-4687-b7ce-ecea27273702
-- title:
--   Theorem 19: eliminating a variable through an equation with coefficient ±1 keeps total unimodularity
-- statement:
--   Let $\begin{pmatrix}A&a_1\\a_2^\top&\alpha\end{pmatrix}$ be a totally unimodular matrix with $\alpha\neq0$. Then the matrix $A-\alpha a_1a_2^\top$ is totally unimodular, and the two systems
--   $$\begin{cases}Ax+a_1y\le b\\ a_2^\top x+\alpha y=\beta\end{cases}\qquad\text{and}\qquad\begin{cases}(A-\alpha a_1a_2^\top)x\le b-\alpha\beta a_1\\ y=\alpha\beta-\alpha a_2^\top x\end{cases}$$
--   are equivalent.
--
--   Combined with Theorem 18, this removes the variable $y_2$ through the equation $h^\top x_A-y_2=0$ and makes progress in the number of variables.
--
--   **Formalization Note** Equivalence means the same solutions $(x,y)\in\mathbb R^n\times\mathbb R$ for all $b\in\mathbb R^k$, $\beta\in\mathbb R$.
--
--   Differences from the source:
--
--   - reading: "the two systems … are equivalent" (domain unspecified) → the same solution sets (x, y) ∈ ℝⁿ × ℝ for every real right-hand side b, β; reason: linear systems are compared on their real solution sets; integer solutions and integer data are a special case
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.11 (PDF p.12), Theorem 19

import Mathlib

open Matrix

namespace CongruencyTU

/-- **Theorem 19** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.11, PDF p.12): "Let (A a₁; a₂⊤ α) be a TU matrix with α ≠ 0. Then, the
matrix A − αa₁a₂⊤ is TU, and the two systems {Ax + a₁y ≤ b, a₂⊤x + αy = β} and
{(A − αa₁a₂⊤)x ≤ b − αβa₁, y = αβ − αa₂⊤x} are equivalent."

**Formalization Note.** `(A a₁; a₂⊤ α)` is `Matrix.fromBlocks A (a₁ as a column) (a₂⊤ as a row) [α]`.
"Equivalent" is read as: the two systems have the same solutions `(x, y) ∈ ℝⁿ × ℝ`, for every
right-hand side `b ∈ ℝᵏ`, `β ∈ ℝ` (this contains the integral case). -/
theorem theorem_19 {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℤ) (a₁ : Fin k → ℤ) (a₂ : Fin n → ℤ)
    (α : ℤ)
    (hTU : (fromBlocks A (replicateCol (Fin 1) a₁) (replicateRow (Fin 1) a₂) !![α]).IsTotallyUnimodular)
    (hα : α ≠ 0) :
    (A - α • vecMulVec a₁ a₂).IsTotallyUnimodular ∧
    ∀ (b : Fin k → ℝ) (β : ℝ) (x : Fin n → ℝ) (y : ℝ),
      ((A.map (Int.cast : ℤ → ℝ)) *ᵥ x + y • (fun i => (a₁ i : ℝ)) ≤ b ∧
          (fun j => (a₂ j : ℝ)) ⬝ᵥ x + (α : ℝ) * y = β) ↔
        (((A - α • vecMulVec a₁ a₂).map (Int.cast : ℤ → ℝ)) *ᵥ x ≤
            b - ((α : ℝ) * β) • (fun i => (a₁ i : ℝ)) ∧
          y = (α : ℝ) * β - (α : ℝ) * ((fun j => (a₂ j : ℝ)) ⬝ᵥ x)) := by sorry

end CongruencyTU
