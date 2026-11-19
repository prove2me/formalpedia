-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_2
-- name    : DiazModulus.dalag_prop_12_2
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:15:48.156916+00:00
-- url     : https://prove2.me/theorems/39bc33c3-09b3-4169-8089-c863c786ea5a
-- title:
--   Waldschmidt 2000 (DALAG), Prop. 12.2 (D. Roy): if E is spanned by k-algebraically independent elements, every matrix over E is k-equivalent to (A B; C 0) with A regular or empty
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A matrix $M$ with $s$ rows, $t$ columns and entries in $K$ *has the block form (A B; C 0) over $k$* if there are a natural number $r \le \min(s, t)$ and invertible matrices $P \in \mathrm{GL}_s(k)$, $Q \in \mathrm{GL}_t(k)$ such that, with $P$ and $Q$ read in $K$, the matrix $N = PMQ$ has $N_{ij} = 0$ whenever $i > r$ and $j > r$ (rows and columns numbered from $1$) and its upper left $r \times r$ block $A$ is invertible: $PMQ = \begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ regular, or empty when $r = 0$.
--
--   Let $(b_j)_{j \in J}$ be a family of elements of $K$, indexed by any set $J$ (finite or not), algebraically independent over $k$, and let $E$ be the $k$-vector space it spans. Then every matrix with entries in $E$, the zero matrix included, has the block form (A B; C 0) over $k$. No hypothesis on $k$ is made.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.2 (p. 419), Proposition 1 of D. Roy (1990), for any field k, by the proof of pp. 420–422; the other proof (p. 424) assumes k infinite and is not used. The zero-size A of the statement is r = 0. In the Remark after Prop. 12.2 (p. 419) the sizes printed for the second and third examples are slips (rows linearly independent: d′ = 0 and ℓ′ = d; columns linearly independent: d′ = d − ℓ and ℓ′ = ℓ); every r ≤ min(s, t) is allowed here, so the three shapes are covered. Proved from DiazModulus.dalag_prop_12_2_ii and DiazModulus.dalag_prop_12_13_i_ii_span. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_2 {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} (b : ι → K)
    (hb : AlgebraicIndependent k b) {s t : ℕ} (M : Matrix (Fin s) (Fin t) K)
    (hM : ∀ i j, M i j ∈ Submodule.span k (Set.range b)) :
    ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  sorry

end DiazModulus
