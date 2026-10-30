-- Prove2me | Theorems.Thm_DiazModulus_sum_boxHilb_le_boxHilb_iInf
-- name    : DiazModulus.sum_boxHilb_le_boxHilb_iInf
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:05:09.677132+00:00
-- url     : https://prove2.me/theorems/bfc41bcb-4d73-4d54-9b4d-f820445066f0
-- title:
--   Separators $P_i \in F_C$, lying in every $I_j$ with $j \ne i$ and regular modulo $I_i$, give $\sum_i h_{I_i}(T) \le h_{\bigcap_i I_i}(T+C)$ (DALAG Ex. 8.5(a), finite level)
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that $F$ is multiplicative ($a \in F_T$ and $b \in F_U$ imply $ab \in F_{T+U}$) and that every $F_T$ is finite-dimensional. Let $\iota$ be a finite type, and for $i \in \iota$ let $I_i$ be an ideal of $S$ and $P_i \in S$; let $C, T \in \mathbb{N}^B$. Assume that $P_i \in F_C$, that $P_i \in I_j$ whenever $j \ne i$, and that $a P_i \in I_i$ implies $a \in I_i$ for every $a \in S$. Then $\sum_i h_{I_i}(T) \le h_{\bigcap_i I_i}(T + C)$ (for $\iota$ empty the intersection is $S$ and both sides are $0$). For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** For each $i$ lift a basis of the image of $F_T$ in $S/I_i$ to elements $e_{i,k} \in F_T$, $k < h_{I_i}(T)$. The products $e_{i,k} P_i$ lie in $F_{T+C}$ and are independent modulo $\bigcap_j I_j$: if $\sum g_{i,k} e_{i,k} P_i \in \bigcap_j I_j$, then for each $j$ the terms with $i \ne j$ lie in $I_j$, so $(\sum_k g_{j,k} e_{j,k}) P_j \in I_j$, hence $\sum_k g_{j,k} e_{j,k} \in I_j$ and all $g_{j,k} = 0$. There are $\sum_i h_{I_i}(T)$ of them, and `DiazModulus.card_le_boxHilb_of_linearIndependent` concludes.
--
--   **Novelty.** Classical; routine formalisation. It is DALAG Exercise 8.5(a) for an abstract filtration, with abstract separators.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Exercise 8.5(a) (pp. 248–249; Chapter 8 is by D. Roy), the injective map A ↦ Σ Aᵢ Pᵢ, here for an abstract filtration and with the separators as hypotheses. Uses DiazModulus.card_le_boxHilb_of_linearIndependent. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem sum_boxHilb_le_boxHilb_iInf {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) {ι : Type*} [Fintype ι] (I : ι → Ideal S) (P : ι → S) (C T : B → ℕ)
    (hPC : ∀ i, P i ∈ F C) (hPI : ∀ i j, i ≠ j → P i ∈ I j)
    (hPreg : ∀ i (a : S), a * P i ∈ I i → a ∈ I i) :
    ∑ i, boxHilb F (I i) T ≤ boxHilb F (⨅ i, I i) (T + C) := by
  sorry

end DiazModulus
