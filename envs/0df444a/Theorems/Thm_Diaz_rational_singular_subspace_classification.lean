-- Prove2me | Theorems.Thm_Diaz_rational_singular_subspace_classification
-- name    : Diaz.rational_singular_subspace_classification
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:08:00.584417+00:00
-- url     : https://prove2.me/theorems/4ffb8c69-6717-4a04-97e3-2a679b283db5
-- title:
--   Rational subspaces of singular 2x2 complex matrices
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and let $S$ be a $\mathbb{C}$-subspace of the $2 \times 2$ complex matrices which is
--
--   * **defined over $K$**: every element of $S$ is a $\mathbb{C}$-linear combination of elements of $S$ all of whose entries lie in $K$;
--   * **singular**: $\det A = 0$ for every $A \in S$;
--   * **non-degenerate at one point**: $S$ contains a matrix $N$ none of whose four entries vanishes.
--
--   Then $\dim_{\mathbb{C}} S \le 2$, and either
--
--   $$S \subseteq \{\, a b^{\mathsf T} : b \in \mathbb{C}^2 \,\} \quad\text{for some } a \in K^2 \text{ with } a_1 a_2 \neq 0,$$
--
--   or the transposed statement holds: there is $b \in K^2$ with $b_1 b_2 \neq 0$ such that every $A \in S$ is $a b^{\mathsf T}$ for some $a \in \mathbb{C}^2$.
--
--   In words: a $K$-rational subspace of the singular $2\times 2$ matrices that meets the open cell where no entry vanishes is at most a plane, and its members either all share one image line or all share one kernel — and that line is spanned by a $K$-rational vector with both coordinates non-zero.
--
--   **Where this sits.** This is the linear-algebra step shared by the proofs of two theorems of Carlo Perassi's, a pair dichotomy (rational proportionality or independence) and a mixed-coordinate rigidity at a Diaz point. In both, a transcendence theorem of Roy and Waldschmidt places a point of a quadric $X_1X_2 = X_3X_4$ inside a $\mathbb{Q}$-rational subspace of that quadric; identifying $\mathbb{C}^4$ with the $2\times 2$ matrices by
--
--   $$\iota(X_1,X_2,X_3,X_4) = \begin{pmatrix} X_1 & X_3 \\ X_4 & X_2 \end{pmatrix}, \qquad \det \circ\, \iota = X_1X_2 - X_3X_4,$$
--
--   turns that subspace into an $S$ as above, and the classification converts it into a rational ratio of two coordinates of the point. He states it for $K = \mathbb{Q}$; nothing in the argument uses more than that $K$ is a field, so it is recorded over an arbitrary subfield of $\mathbb{C}$.
--
--   **Proof idea.** For $2 \times 2$ matrices the determinant is a quadratic form whose polarisation is
--
--   $$\beta(A,B) = A_{11}B_{22} + A_{22}B_{11} - A_{12}B_{21} - A_{21}B_{12}, \qquad \det(A+B) = \det A + \det B + \beta(A,B),$$
--
--   so singularity of the whole of $S$ is equivalent to $\det = 0$ on $S$ together with $\beta \equiv 0$ on $S \times S$. Writing two singular matrices as $A = pq^{\mathsf T}$ and $B = rs^{\mathsf T}$ gives the factorisation
--
--   $$\beta(A,B) = (p_1 r_2 - p_2 r_1)(q_1 s_2 - q_2 s_1),$$
--
--   that is, $\beta(A,B) = 0$ exactly when $A$ and $B$ share an image line or share a kernel. This is the Segre picture: the singular matrices form the cone over $\mathbb{P}^1 \times \mathbb{P}^1$, and a linear space inside it is a line of one of the two rulings.
--
--   **Proof.** Write $N = pq^{\mathsf T}$; since no entry $N_{ij} = p_i q_j$ vanishes, all $p_i$ and all $q_j$ are non-zero.
--
--   *Dichotomy.* Suppose some $A \in S$ does not have image inside $\mathbb{C}p$. Factor $A = rs^{\mathsf T}$. From $\beta(N,A) = 0$ and $r \notin \mathbb{C}p$ we get $q_1 s_2 - q_2 s_1 = 0$, so $s = \lambda q$ with $\lambda \neq 0$. Now let $B = tw^{\mathsf T}$ be any element of $S$. If $w \notin \mathbb{C}q$, then $\beta(N,B) = 0$ forces $t \in \mathbb{C}p$, while $\beta(A,B) = 0$ forces $t \in \mathbb{C}r$; as $r \notin \mathbb{C}p$ this gives $t = 0$ and $B = 0$. Hence every $B \in S$ has $w \in \mathbb{C}q$, i.e. all rows of all elements of $S$ are multiples of $q^{\mathsf T}$. So either every element of $S$ has image inside $\mathbb{C}p$, or every element of $S$ has rows inside $\mathbb{C}q^{\mathsf T}$.
--
--   *Rationality.* Since $S$ is defined over $K$ and $N \neq 0$, some $M \in S$ with all entries in $K$ is non-zero. In the first case $M = p b^{\mathsf T}$ with $b_{j_0} \neq 0$ for some $j_0$, and the $j_0$-th column $a := M_{\bullet j_0} = b_{j_0} p$ is a $K$-rational vector spanning $\mathbb{C}p$; both its entries are non-zero because those of $p$ are. Every $A \in S$ is then $a b'^{\mathsf T}$ after rescaling. The second case is the transpose.
--
--   *Dimension.* In either case $S$ is contained in the range of a linear map $\mathbb{C}^2 \to \mathrm{M}_2(\mathbb{C})$, whence $\dim_{\mathbb{C}} S \le 2$.
--
--   **Remarks on the formalisation.** "Defined over $K$" is the hypothesis $S \le \operatorname{span}_{\mathbb{C}}\{A \in S : A_{ij} \in K \ \forall i,j\}$; the reverse inclusion is automatic, so this says exactly that $S$ is the complex span of its $K$-rational points. The rank-one factorisation of a singular $2\times2$ matrix is reproved inline rather than imported, since a solution file is self-contained; it is the same argument as in `Diaz.rank_one_of_det_eq_zero`, and the polarisation identity is `Diaz.det_add_two`.
--
--   The hypothesis that $N$ has no zero entry cannot be dropped. The matrices with second row zero form a $K$-rational plane of singular matrices whose common image line is spanned by $(1,0)$ and by nothing with two non-zero coordinates; that plane simply contains no matrix with four non-zero entries. The bound $\dim_{\mathbb{C}} S \le 2$ is sharp: for $a = (1,1)$ the plane of matrices with two equal rows satisfies every hypothesis, with $N$ the all-ones matrix.
--
--   **What is deliberately not claimed.** Nothing about transcendence. This node does not assert that the subspace $S$ exists in the situations of those two theorems — that is Théorème 0.2, respectively Théorème 7.1, of Roy–Waldschmidt (1997), which is not available in this Mathlib revision. This is only the elementary half: *given* the rational subspace, this is what it looks like.
--
--   Elementary. Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.rational_singular_subspace_classification
    {K : Subfield ℂ} {S : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ)}
    (hK : S ≤ Submodule.span ℂ {A : Matrix (Fin 2) (Fin 2) ℂ | A ∈ S ∧ ∀ i j, A i j ∈ K})
    (hsing : ∀ A ∈ S, A.det = 0)
    {N : Matrix (Fin 2) (Fin 2) ℂ} (hN : N ∈ S) (hN0 : ∀ i j, N i j ≠ 0) :
    Module.finrank ℂ S ≤ 2 ∧
      ((∃ a : Fin 2 → ℂ, (∀ i, a i ∈ K) ∧ (∀ i, a i ≠ 0) ∧
          ∀ A ∈ S, ∃ b : Fin 2 → ℂ, ∀ i j, A i j = a i * b j) ∨
       (∃ b : Fin 2 → ℂ, (∀ j, b j ∈ K) ∧ (∀ j, b j ≠ 0) ∧
          ∀ A ∈ S, ∃ a : Fin 2 → ℂ, ∀ i j, A i j = a i * b j)) := by sorry
