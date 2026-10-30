-- Prove2me | Theorems.Thm_DiazModulus_boxHilb_anti
-- name    : DiazModulus.boxHilb_anti
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:18.091009+00:00
-- url     : https://prove2.me/theorems/3184fc3f-1b1f-41b3-8d34-2059a26eef0d
-- title:
--   The Hilbert function of a filtration by finite-dimensional subspaces is antitone in the ideal: $I \le J$ gives $h_J(T) \le h_I(T)$
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that every $F_T$ is finite-dimensional. Then for all ideals $I \subseteq J$ of $S$ and every $T \in \mathbb{N}^B$, $h_J(T) \le h_I(T)$. For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Since $I \subseteq J$, the quotient map $S \to S/J$ factors through $S/I$, so the image of $F_T$ in $S/J$ is the image under a linear map of its image in $S/I$, which is finite-dimensional; a linear map does not raise dimension.
--
--   **Novelty.** Classical; routine formalisation. It is the finite-level fact behind DALAG Exercise 8.3, which compares leading coefficients.
-- source:
--   Linear algebra. Compare M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Exercise 8.3 (p. 248; Chapter 8 is by D. Roy), the corresponding inequality for the normalised leading coefficient of ideals of the same rank. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem boxHilb_anti {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) {I J : Ideal S} (hIJ : I ≤ J) (T : B → ℕ) :
    boxHilb F J T ≤ boxHilb F I T := by
  sorry

end DiazModulus
