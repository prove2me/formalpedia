-- Prove2me | Theorems.Thm_DiazModulus_exists_boxHilb_family
-- name    : DiazModulus.exists_boxHilb_family
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:44.816958+00:00
-- url     : https://prove2.me/theorems/dbf4245c-31dc-4084-abb9-a8fd13a06b85
-- title:
--   $F_T$ contains $h_I(T)$ elements that are linearly independent modulo $I$ and span $F_T$ modulo $I$
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that every $F_T$ is finite-dimensional. Then for every ideal $I$ of $S$ and every $T \in \mathbb{N}^B$ there are $N = h_I(T)$ elements $e_1, \dots, e_N$ of $F_T$ whose classes in $S/I$ are linearly independent over $K$, such that every $x \in F_T$ is congruent modulo $I$ to an element of the $K$-span of $e_1, \dots, e_N$ (for $N = 0$ the family is empty and $F_T \subseteq I$). For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Take a basis $b_1, \dots, b_N$ of the image $W$ of $F_T$ in $S/I$ and lift each $b_i$ to some $e_i \in F_T$. The classes of the $e_i$ are the $b_i$, hence independent, and the image of the span of the $e_i$ is the span of the $b_i$, which is $W$; so each $x \in F_T$ has the class of some $y$ in that span, that is, $x - y \in I$.
--
--   **Novelty.** Classical; routine formalisation. Compare the space $E$ in the proof of DALAG Th. 8.18 (p. 245).
-- source:
--   Linear algebra. Compare the subspace E of dimension H(J; D₀, D) in the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.18 (§8.3.3, p. 245; Chapter 8 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem exists_boxHilb_family {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) (T : B → ℕ) :
    ∃ e : Fin (boxHilb F I T) → S, (∀ i, e i ∈ F T) ∧
      LinearIndependent K (fun i => Ideal.Quotient.mk I (e i)) ∧
      ∀ x ∈ F T, ∃ y ∈ Submodule.span K (Set.range e), x - y ∈ I := by
  sorry

end DiazModulus
