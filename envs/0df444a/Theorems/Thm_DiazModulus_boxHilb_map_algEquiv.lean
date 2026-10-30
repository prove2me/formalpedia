-- Prove2me | Theorems.Thm_DiazModulus_boxHilb_map_algEquiv
-- name    : DiazModulus.boxHilb_map_algEquiv
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:35.559397+00:00
-- url     : https://prove2.me/theorems/278ebeae-8e03-467d-bf8b-e7687d92371c
-- title:
--   An algebra automorphism $\sigma$ with $\sigma(F_T) = F_T$ preserves the Hilbert function: $h_{\sigma(I)}(T) = h_I(T)$
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Let $\sigma$ be a $K$-algebra automorphism of $S$, $I$ an ideal of $S$ and $T \in \mathbb{N}^B$ with $\sigma(F_T) = F_T$. Then $h_{\sigma(I)}(T) = h_I(T)$, where $\sigma(I)$ is the image ideal. No finiteness hypothesis is needed (a `Module.finrank` of an infinite-dimensional space is $0$ on both sides). For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** $\sigma$ induces a $K$-algebra isomorphism $\varphi : S/I \to S/\sigma(I)$ with $\varphi \circ q_I = q_{\sigma(I)} \circ \sigma$. Since $\sigma(F_T) = F_T$, the image of $F_T$ in $S/\sigma(I)$ is $\varphi$ of its image in $S/I$, and a linear isomorphism preserves the dimension of a subspace.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Linear algebra. Used for translates as in M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §5.3.2 (Chapter 5 is by D. Roy), at finite level. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem boxHilb_map_algEquiv {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (σ : S ≃ₐ[K] S) (I : Ideal S) (T : B → ℕ)
    (hσ : (F T).map σ.toLinearMap = F T) :
    boxHilb F (I.map σ) T = boxHilb F I T := by
  sorry

end DiazModulus
