-- Prove2me | Theorems.Thm_DiazModulus_generic_matrix_coefficient_barrier
-- name    : DiazModulus.generic_matrix_coefficient_barrier
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:32:39.253094+00:00
-- url     : https://prove2.me/theorems/659cad29-bb2b-4c74-ae41-b5a7db731557
-- title:
--   The Matrix Coefficient Conjecture holds for singular n×n matrices over ℚu + ℚū + ℚiπ (and over Q̄) at a generic point
-- statement:
--   Let $u \neq 0$ with $|u|^2$ algebraic, and suppose $u$ and $\pi$ are algebraically independent over $\overline{\mathbb{Q}}$ (a *generic* point of the circle $|z|^2 = |u|^2$).
--
--   - Every singular $n \times n$ matrix $M$ with entries in $\mathbb{Q}u + \mathbb{Q}\bar u + \mathbb{Q}i\pi$ has non-zero $v, w \in \mathbb{Q}^n$ with $w^{\mathsf T}Mv = 0$.
--   - Every singular $n \times n$ matrix $M$ with entries in $\overline{\mathbb{Q}}u + \overline{\mathbb{Q}}\bar u + \overline{\mathbb{Q}}i\pi$ has such $v, w \in \overline{\mathbb{Q}}^n$.
--
--   At a candidate of Diaz's conjecture, $u$, $\bar u$ and $i\pi$ are logarithms of algebraic numbers. So on these matrices the Matrix Coefficient Conjecture of Dasgupta and Kakde (their Conjecture 1.2), and its $\overline{\mathbb{Q}}$ form (Conjecture 2.3), are theorems in every size: like the four exponentials conjecture at $n = 2$ (`DiazModulus.generic_qbar_homogeneous_four_exp_barrier`), they cannot detect a generic candidate through its homogeneous data.
--
--   **Proof.** Write $M = Au + B\bar u + C\,i\pi$. The polynomial $\det(AX_0 + BX_1 + CX_2)$ is homogeneous of degree $n$ and vanishes at $(u, \bar u, i\pi)$, so it is zero (`DiazModulus.generic_no_homogeneous_relation`). Hence every matrix in the span of $A, B, C$ is singular, and Roy's lemma (`Transcendence.singular_matrix_subspace_annihilating_pair`), over $\overline{\mathbb{Q}}$ or over $\mathbb{Q}$, gives $v, w$.
--
--   **Novelty.** None asserted. Not found stated in the sources read; it also follows from Waldschmidt's Proposition 12.2 with the Remark on p. 424 of *Diophantine Approximation on Linear Algebraic Groups* (Property $\left(\begin{smallmatrix} A & B\\ C & 0\end{smallmatrix}\right)$ for spaces spanned by $1$ and algebraically independent elements). The book records the conjecture that this property holds for $(\mathbb{Q}, \mathbb{C}, \mathcal{L})$ (§12.4.1); for square matrices that property implies the Matrix Coefficient Conjecture. The contribution of this node is the formal proof.
-- source:
--   The conjectures: S. Dasgupta and M. Kakde, Ranks of matrices of logarithms of algebraic numbers II: the Matrix Coefficient Conjecture, arXiv:2408.08178 (2024), Conjectures 1.2 and 2.3 (pp. 2–3). Also a consequence of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 12.2 and the Remark on p. 424; compare §12.4.1 (p. 437). Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate Matrix

namespace DiazModulus

/-- For `u ≠ 0` with `|u|²` algebraic and `u`, `π` algebraically independent: every singular `n × n`
matrix with entries in `ℚ u + ℚ ū + ℚ iπ` has non-zero `v, w ∈ ℚⁿ` with `wᵀ M v = 0`, and every singular
`n × n` matrix with entries in `Q̄ u + Q̄ ū + Q̄ iπ` has such `v, w ∈ Q̄ⁿ`. These are the Matrix Coefficient
Conjecture of Dasgupta and Kakde and its `Q̄` form, on these matrices. -/
theorem generic_matrix_coefficient_barrier (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I]) (n : ℕ) :
    (∀ M : Matrix (Fin n) (Fin n) ℂ,
      (∀ i j, ∃ a b c : ℚ, M i j = a * u + b * conj u + c * (((Real.pi : ℝ) : ℂ) * Complex.I)) →
      M.det = 0 →
      ∃ v w : Fin n → ℚ, v ≠ 0 ∧ w ≠ 0 ∧
        (fun i => (w i : ℂ)) ⬝ᵥ (M *ᵥ (fun i => (v i : ℂ))) = 0) ∧
    (∀ M : Matrix (Fin n) (Fin n) ℂ,
      (∀ i j, M i j ∈ Submodule.span Qbar ({u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ)) →
      M.det = 0 →
      ∃ v w : Fin n → ℂ, v ≠ 0 ∧ w ≠ 0 ∧ (∀ i, v i ∈ Qbar) ∧ (∀ i, w i ∈ Qbar) ∧
        w ⬝ᵥ (M *ᵥ v) = 0) := by
  sorry

end DiazModulus
