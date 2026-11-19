-- Prove2me | Theorems.Thm_DiazModulus_dalag_remark_12_1_3
-- name    : DiazModulus.dalag_remark_12_1_3
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:06.307237+00:00
-- url     : https://prove2.me/theorems/417f6926-6f7c-45a6-b0e6-465003adf9c4
-- title:
--   Waldschmidt 2000 (DALAG), Remark p. 424: if E₀ is spanned by k-algebraically independent elements, then k + E₀ has Property (A B; C 0) (any k; E₀ ∩ k = {0} is automatic)
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A matrix $M$ with $s$ rows, $t$ columns and entries in $K$ *has the block form (A B; C 0) over $k$* if there are a natural number $r \le \min(s, t)$ and invertible matrices $P \in \mathrm{GL}_s(k)$, $Q \in \mathrm{GL}_t(k)$ such that, with $P$ and $Q$ read in $K$, the matrix $N = PMQ$ has $N_{ij} = 0$ whenever $i > r$ and $j > r$ (rows and columns numbered from $1$) and its upper left $r \times r$ block $A$ is invertible: $PMQ = \begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ regular, or empty when $r = 0$. A $k$-vector subspace $E$ of $K$ has *Property (A B; C 0)* (DALAG §12.1.3) if every non-zero matrix with entries in $E$ has the block form (A B; C 0) over $k$.
--
--   Let $(b_j)_{j \in J}$ be a family of elements of $K$, indexed by any set $J$ (finite or not), algebraically independent over $k$. Let $E_0$ be the $k$-vector space it spans, and $k + E_0$ the $k$-vector space spanned by $1$ and $E_0$. Then $k + E_0$ has Property (A B; C 0): every non-zero matrix with entries in $k + E_0$ has the block form (A B; C 0) over $k$. No hypothesis on $k$ is made, and the printed hypothesis $E_0 \cap k = \{0\}$ is not assumed: it follows from the algebraic independence of the $b_j$.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Remark in §12.1.3 (p. 424), for any field k and without the hypothesis E₀ ∩ k = {0}, which follows from the algebraic independence (a non-zero c ∈ E₀ ∩ k would be a non-zero polynomial relation of degree at most 1). The statement of the Remark is correct, but its printed reason has a gap: Property (A B; C 0) is a property of the triple (k, K, E), not of the k-vector space E, so the k-linear isomorphism of k + E₀ with kX + E₀ in K(X) does not carry it. The proof here does not pass through K(X): the inductive proof of Prop. 12.2 (pp. 420–422) is run on k + E₀ directly (DiazModulus.dalag_prop_12_2_ii), with the hyperplane E₁ of its induction chosen to contain 1; the printed step "x ∉ E₁, hence x is transcendental over k(E₁)" (Lemma 12.3) fails for k + E₀ whenever 1 lies in the span of the entries but not in E₁. Proved from DiazModulus.dalag_prop_12_2_ii and DiazModulus.dalag_prop_12_13_i_ii_span. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_remark_12_1_3 {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} (b : ι → K)
    (hb : AlgebraicIndependent k b) :
    ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K),
      (∀ i j, M i j ∈ Submodule.span k {(1 : K)} ⊔ Submodule.span k (Set.range b)) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  sorry

end DiazModulus
