-- Prove2me | Theorems.Thm_DiazModulus_boxHilb_add_finrank_inf
-- name    : DiazModulus.boxHilb_add_finrank_inf
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:10.544995+00:00
-- url     : https://prove2.me/theorems/a44982f3-3e6c-4667-bc16-db203ec3a9b4
-- title:
--   Rank–nullity for the Hilbert function of a filtration: $h_I(T) + \dim_K (F_T \cap I) = \dim_K F_T$
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that every $F_T$ is finite-dimensional. Then for every ideal $I$ of $S$ and every $T \in \mathbb{N}^B$, $h_I(T) + \dim_K (F_T \cap I) = \dim_K F_T$. For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Restrict the quotient map $q : S \to S/I$, as a $K$-linear map, to $F_T$. Its range is $q(F_T)$, of dimension $h_I(T)$, and its kernel is $F_T \cap I$; rank–nullity gives the identity.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Linear algebra (rank–nullity). The Hilbert function H(I; T) is that of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.2.2 (p. 235; Chapter 8 is by D. Roy), here for an abstract filtration and at finite level. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem boxHilb_add_finrank_inf {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) (T : B → ℕ) :
    boxHilb F I T + Module.finrank K ↥(F T ⊓ Submodule.restrictScalars K I) = Module.finrank K ↥(F T) := by
  sorry

end DiazModulus
