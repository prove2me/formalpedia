-- Prove2me | Theorems.Thm_DiazModulus_dalag_conclusion_12_1_6
-- name    : DiazModulus.dalag_conclusion_12_1_6
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:41.458173+00:00
-- url     : https://prove2.me/theorems/2b65057f-29d6-4f79-b5a9-0807695a77d8
-- title:
--   Waldschmidt 2000 (DALAG), §12.1.6: for E ∋ 1, if every matrix over E has rank equal to its structural rank, then E has Property (A B; C 0)
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A matrix $M$ with $s$ rows, $t$ columns and entries in $K$ *has the block form (A B; C 0) over $k$* if there are a natural number $r \le \min(s, t)$ and invertible matrices $P \in \mathrm{GL}_s(k)$, $Q \in \mathrm{GL}_t(k)$ such that, with $P$ and $Q$ read in $K$, the matrix $N = PMQ$ has $N_{ij} = 0$ whenever $i > r$ and $j > r$ (rows and columns numbered from $1$) and its upper left $r \times r$ block $A$ is invertible: $PMQ = \begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ regular, or empty when $r = 0$. A $k$-vector subspace $E$ of $K$ has *Property (A B; C 0)* (DALAG §12.1.3) if every non-zero matrix with entries in $E$ has the block form (A B; C 0) over $k$.
--
--   Let $E \subseteq K$ be a $k$-vector subspace with $1 \in E$ satisfying condition (iv) of DALAG Prop. 12.13, in presentation form: whenever $e_1, \dots, e_m \in E$ are linearly independent over $k$ and $N_1, \dots, N_m$ are $s \times t$ matrices with entries in $k$, the matrix $M = \sum_{j=1}^m e_j N_j$ satisfies $\operatorname{rank}_K M = \operatorname{rank}_{k(Z_1, \dots, Z_m)} \sum_{j=1}^m Z_j N_j$ (for all $s$, $t$, $m$). The right-hand side is the rank of the generic matrix over the field of rational functions in $Z_1, \dots, Z_m$: the structural rank of $M$ over $k$ (DALAG §12.1.4), computed from the presentation $M = \sum_j e_j N_j$. Then $E$ has Property (A B; C 0).
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §12.1.6 (p. 431): "Property (A B; C 0) is a consequence of r = r_str", said there for E = k + E₀ with E₀ ∩ k = {0}; any E containing 1 is of this form (E₀ a complement of k·1 in E), so E₀ does not appear. In the same sentence, "as pointed out in § 12.1.5" refers to the boxed statement of p. 427, which is in § 12.1.4. Proved from DiazModulus.dalag_prop_12_13_iv_iii, DiazModulus.dalag_prop_12_13_iii_ii and DiazModulus.dalag_prop_12_2_ii. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_conclusion_12_1_6 {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (h1 : (1 : K) ∈ E)
    (hiv : ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
      (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e → (∀ j, e j ∈ E) →
      M = ∑ j, e j • (N j).map (algebraMap k K) →
      M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank) :
    ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  sorry

end DiazModulus
