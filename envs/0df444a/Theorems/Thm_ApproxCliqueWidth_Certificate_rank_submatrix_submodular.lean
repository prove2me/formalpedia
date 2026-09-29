-- Prove2me | Theorems.Thm_ApproxCliqueWidth_Certificate_rank_submatrix_submodular
-- name    : ApproxCliqueWidth.Certificate.rank_submatrix_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:33:27.963157+00:00
-- url     : https://prove2.me/theorems/a747554a-5718-4d27-b3dd-9396cba5d1dc
-- title:
--   Proposition 6.1 — submodularity of the rank of submatrices
-- statement:
--   Let $M = (m_{ij} : i \in R,\ j \in C)$ be a matrix over a field $F$, with $R$ and $C$ finite. For all $X_1, X_2 \subseteq R$ and $Y_1, Y_2 \subseteq C$,
--   $$\mathrm{rk}\big(M[X_1, Y_1]\big) + \mathrm{rk}\big(M[X_2, Y_2]\big) \ge \mathrm{rk}\big(M[X_1 \cup X_2, Y_1 \cap Y_2]\big) + \mathrm{rk}\big(M[X_1 \cap X_2, Y_1 \cup Y_2]\big).$$
--
--   This rank inequality is the linear-algebra input behind the submodularity of cut-rank; it is not in Mathlib.
--
--   **Formalization Note** $M[X, Y]$ is `Matrix.submatrix` with rows and columns indexed by the elements of the finite sets $X$ and $Y$; ranks are natural numbers and the field $F$ is arbitrary.
-- source:
--   Oum and Seymour, Approximating clique-width and branch-width, J. Combin. Theory Ser. B 96 (2006) 514–528, p. 522, Proposition 6.1

import Mathlib

namespace ApproxCliqueWidth.Certificate

/-- Oum–Seymour Proposition 6.1 (p. 522): submodularity of the rank of submatrices,
`rk M[X₁, Y₁] + rk M[X₂, Y₂] ≥ rk M[X₁ ∪ X₂, Y₁ ∩ Y₂] + rk M[X₁ ∩ X₂, Y₁ ∪ Y₂]`. -/
theorem rank_submatrix_submodular {F R C : Type*} [Field F] [Fintype R] [Fintype C]
    [DecidableEq R] [DecidableEq C] (M : Matrix R C F) (X₁ X₂ : Finset R) (Y₁ Y₂ : Finset C) :
    (M.submatrix (fun i : ↥(X₁ ∪ X₂) => (i : R)) (fun j : ↥(Y₁ ∩ Y₂) => (j : C))).rank +
        (M.submatrix (fun i : ↥(X₁ ∩ X₂) => (i : R)) (fun j : ↥(Y₁ ∪ Y₂) => (j : C))).rank ≤
      (M.submatrix (fun i : ↥X₁ => (i : R)) (fun j : ↥Y₁ => (j : C))).rank +
        (M.submatrix (fun i : ↥X₂ => (i : R)) (fun j : ↥Y₂ => (j : C))).rank := by sorry

end ApproxCliqueWidth.Certificate
