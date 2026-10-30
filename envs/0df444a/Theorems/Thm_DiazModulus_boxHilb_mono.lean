-- Prove2me | Theorems.Thm_DiazModulus_boxHilb_mono
-- name    : DiazModulus.boxHilb_mono
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:22.354784+00:00
-- url     : https://prove2.me/theorems/a678a990-3ccf-41a5-8f3f-eb04936a918f
-- title:
--   The Hilbert function of a monotone filtration by finite-dimensional subspaces is monotone: $T \le T'$ gives $h_I(T) \le h_I(T')$
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that $F$ is monotone ($T \le T'$ coordinatewise implies $F_T \subseteq F_{T'}$) and that every $F_T$ is finite-dimensional. Then for every ideal $I$ of $S$ and all $T \le T'$ in $\mathbb{N}^B$ (coordinatewise), $h_I(T) \le h_I(T')$. For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** $F_T \subseteq F_{T'}$, so the image of $F_T$ in $S/I$ lies in the image of $F_{T'}$, which is finite-dimensional; dimension is monotone on subspaces of a finite-dimensional space.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Linear algebra. The Hilbert function is that of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.2.2 (p. 235; Chapter 8 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem boxHilb_mono {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmono : Monotone F) (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) {T T' : B → ℕ} (hT : T ≤ T') :
    boxHilb F I T ≤ boxHilb F I T' := by
  sorry

end DiazModulus
