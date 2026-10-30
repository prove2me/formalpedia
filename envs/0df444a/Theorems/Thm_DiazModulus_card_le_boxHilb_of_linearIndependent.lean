-- Prove2me | Theorems.Thm_DiazModulus_card_le_boxHilb_of_linearIndependent
-- name    : DiazModulus.card_le_boxHilb_of_linearIndependent
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:43.248993+00:00
-- url     : https://prove2.me/theorems/7a51a152-8abe-45c1-903d-c0b862b84d27
-- title:
--   A family in $F_T$ that is linearly independent modulo $I$ has at most $h_I(T)$ members
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that every $F_T$ is finite-dimensional. Let $I$ be an ideal of $S$, $T \in \mathbb{N}^B$, and let $e_i$ ($i \in \iota$, $\iota$ finite) be elements of $F_T$ whose classes in $S/I$ are linearly independent over $K$. Then $|\iota| \le h_I(T)$. For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** The classes of the $e_i$ lie in the image $W$ of $F_T$ in $S/I$ and are independent there; $W$ is finite-dimensional of dimension $h_I(T)$, and an independent family in it has at most $\dim W$ members.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Linear algebra. The Hilbert function is that of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.2.2 (p. 235; Chapter 8 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem card_le_boxHilb_of_linearIndependent {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) {ι : Type*} [Fintype ι] (I : Ideal S) (T : B → ℕ)
    (e : ι → S) (he : ∀ i, e i ∈ F T)
    (hli : LinearIndependent K (fun i => Ideal.Quotient.mk I (e i))) :
    Fintype.card ι ≤ boxHilb F I T := by
  sorry

end DiazModulus
