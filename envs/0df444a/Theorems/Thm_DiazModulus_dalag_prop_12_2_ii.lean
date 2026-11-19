-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_2_ii
-- name    : DiazModulus.dalag_prop_12_2_ii
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:49.670206+00:00
-- url     : https://prove2.me/theorems/2e6b38b4-bca5-40bf-aa28-844024cb0fde
-- title:
--   Waldschmidt 2000 (DALAG), Prop. 12.2, inductive proof, for any E in which 1, x k-free implies x alg. indep.: every matrix over E is k-equivalent to (A B; C 0), A regular or empty
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A matrix $M$ with $s$ rows, $t$ columns and entries in $K$ *has the block form (A B; C 0) over $k$* if there are a natural number $r \le \min(s, t)$ and invertible matrices $P \in \mathrm{GL}_s(k)$, $Q \in \mathrm{GL}_t(k)$ such that, with $P$ and $Q$ read in $K$, the matrix $N = PMQ$ has $N_{ij} = 0$ whenever $i > r$ and $j > r$ (rows and columns numbered from $1$) and its upper left $r \times r$ block $A$ is invertible: $PMQ = \begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ regular, or empty when $r = 0$. Let $E \subseteq K$ be a $k$-vector subspace satisfying condition (ii) of DALAG Prop. 12.13: whenever $x_1, \dots, x_n \in E$ ($n \ge 0$) and $1, x_1, \dots, x_n$ are linearly independent over $k$, the elements $x_1, \dots, x_n$ are algebraically independent over $k$.
--
--   Then every matrix with entries in $E$, the zero matrix included, has the block form (A B; C 0) over $k$. No hypothesis on $k$ is made, and $1 \in E$ is not assumed.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.2 (p. 419), by its proof on pp. 420–422, which needs no hypothesis on k, run for any subspace E with property (ii) of Prop. 12.13 in place of a span of algebraically independent elements. DALAG remarks (p. 422) that this proof yields a more general result, where the xᵢ are not assumed algebraically independent (it cites Roy 1989); this is such a generalisation. The hyperplane E₁ of the induction on the dimension of the span of the entries is chosen to contain 1 when possible (DiazModulus.dalag_prop_12_2_split); the step is DiazModulus.dalag_prop_12_2_step. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_2_ii {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
      LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x)
    {s t : ℕ} (M : Matrix (Fin s) (Fin t) K) (hM : ∀ i j, M i j ∈ E) :
    ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  sorry

end DiazModulus
