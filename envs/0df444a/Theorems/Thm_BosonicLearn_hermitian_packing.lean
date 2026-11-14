-- Prove2me | Theorems.Thm_BosonicLearn_hermitian_packing
-- name    : BosonicLearn.hermitian_packing
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:10:38.77867+00:00
-- url     : https://prove2.me/theorems/4cfa4800-117f-4288-8970-27f5b297a4b3
-- title:
--   A packing of the operator-norm ball of traceless Hermitian matrices: $e^{\Omega(n^2)}$ points, pairwise $\|X-Y\|_F^2\ge bn$
-- statement:
--   The metric-entropy statement behind the size $M=2^{\Theta(n^2)}$ of the hard ensemble of Theorem 9.
--
--   There are absolute constants $b,c>0$ and $n_0$ such that for every $n\ge n_0$ there is a finite set $T$ of traceless Hermitian $n\times n$ matrices with $-4\cdot\mathbf 1\preceq X\preceq4\cdot\mathbf 1$ (i.e. $T\subset G_{\rm supp}$), of cardinality at least $e^{cn^2}$, such that $\|X-Y\|_F^2=\operatorname{Tr}(X-Y)^2\ge bn$ for all distinct $X,Y\in T$.
--
--   Proof idea: embed real $s\times s$ matrices, $s=\lfloor n/2\rfloor$, as $X(A)=s^{-1/2}\begin{pmatrix}0&A\\A^T&0\end{pmatrix}$. A standard Gaussian $A$ has $\|A\|\le4\sqrt s$ with probability $\ge\frac12$ (`GaussianMatrix.extreme_singular_values_deviation`), every Frobenius ball of radius $\sqrt{s^2/8}$ has Gaussian measure $\le e^{-s^2/4}$ (Chernoff), and a greedy choice gives $e^{s^2/8}$ separated points in the good set.
--
--   **Formalization Note** The operator-norm bound is written as two Loewner inequalities and the squared Frobenius distance as `((X - Y) * (X - Y)).trace.re`. The paper's ensemble of rotated projectors (Eq. (223)) is replaced by this statement.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §8, proof of Theorem 9, pp. 65–67 (Eq. (223): "a size $M=2^{\Theta(n^2)}$ ensemble"); §5.1, p. 30 ($G_{\rm supp}$)

import Mathlib

open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **A packing of the operator-norm ball of traceless Hermitian matrices of size `exp(Ω(n²))`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §8, proof of Theorem 9, Eq. (223), p. 66 ("a size M = 2^{Θ(n²)} ensemble"), and §5.1, p. 30 (`G_supp = {X ∈ Herm_0(n) : ‖X‖_op ≤ 4}`).

There are absolute constants `b, c > 0` and `n₀` such that for every `n ≥ n₀` there is a finite set `T` of traceless
Hermitian `n × n` matrices with `−4·1 ⪯ X ⪯ 4·1`, of cardinality at least `exp(c n²)`, any two distinct members of which
satisfy `‖X − Y‖_F² = Tr (X − Y)² ≥ b n`.

**Formalization Note.** The operator-norm bound is written as two Loewner inequalities and the Frobenius distance as
`Re Tr((X − Y)(X − Y))`. The paper's ensemble (rotated projectors) is replaced by this metric-entropy statement, which
is what the packing argument uses; it follows from the Gaussian measure of the operator-norm ball
(`GaussianMatrix.extreme_singular_values_deviation`) and of Frobenius balls. -/
theorem hermitian_packing :
    ∃ b : ℝ, 0 < b ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ T : Finset (Matrix (Fin n) (Fin n) ℂ),
        Real.exp (c * (n : ℝ) ^ 2) ≤ (T.card : ℝ) ∧
        (∀ X ∈ T, X.IsHermitian ∧ X.trace = 0 ∧
          (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
          (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef) ∧
        ∀ X ∈ T, ∀ Y ∈ T, X ≠ Y → b * n ≤ ((X - Y) * (X - Y)).trace.re := by sorry

end BosonicLearn
