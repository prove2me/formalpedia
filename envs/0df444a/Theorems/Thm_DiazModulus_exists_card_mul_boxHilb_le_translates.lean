-- Prove2me | Theorems.Thm_DiazModulus_exists_card_mul_boxHilb_le_translates
-- name    : DiazModulus.exists_card_mul_boxHilb_le_translates
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:48.294001+00:00
-- url     : https://prove2.me/theorems/c5e44038-0aa5-4a61-8975-bed482e17f60
-- title:
--   For $N$ pairwise comaximal images $\sigma_i(H)$ under filtration-preserving automorphisms, $N\,h_H(T) \le h_{\bigcap_i \sigma_i(H)}(T+C)$ for some fixed $C$
-- statement:
--   Let $K$ be a field, $S$ a commutative $K$-algebra, $B$ a type, and $F$ a family of $K$-subspaces $F_T$ of $S$ indexed by $T \in \mathbb{N}^B$ (a filtration, on which only the hypotheses listed are assumed). Assume that $F$ is monotone ($T \le T'$ coordinatewise implies $F_T \subseteq F_{T'}$), that $F$ is multiplicative ($a \in F_T$ and $b \in F_U$ imply $ab \in F_{T+U}$), that every $F_T$ is finite-dimensional and that $F$ is exhaustive (every element of $S$ lies in some $F_T$). Let $\iota$ be a finite type with $N$ elements, $H$ an ideal of $S$ and $\sigma_i$ ($i \in \iota$) $K$-algebra automorphisms of $S$ with $\sigma_i(F_T) = F_T$ for every $i$ and every $T$, such that $\sigma_i(H) + \sigma_j(H) = S$ whenever $i \ne j$. Then there is $C \in \mathbb{N}^B$ such that $N\,h_H(T) \le h_{\bigcap_i \sigma_i(H)}(T + C)$ for every $T \in \mathbb{N}^B$. For an ideal $I$ of $S$, $h_I(T)$ is `boxHilb F I T`, the dimension over $K$ of the image of $F_T$ in $S/I$ (DALAG's $H(I; T)$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Write $J_i = \sigma_i(H)$. For $i \ne j$, comaximality gives $x + y = 1$ with $x \in J_i$, $y \in J_j$, so $q_{ij} = y \in J_j$ is $\equiv 1$ modulo $J_i$; then $P_i = \prod_{j \ne i} q_{ij}$ lies in every $J_j$ with $j \ne i$ and is $\equiv 1$ modulo $J_i$, so $a P_i \in J_i$ forces $a \in J_i$. Each $P_i$ lies in some $F_{T_i}$ (exhaustion), hence in $F_C$ with $C = \sum_i T_i$. `DiazModulus.sum_boxHilb_le_boxHilb_iInf` gives $\sum_i h_{J_i}(T) \le h_{\bigcap J_i}(T + C)$, and $h_{J_i}(T) = h_H(T)$ by `DiazModulus.boxHilb_map_algEquiv`. The shift $C$ depends only on the separators.
--
--   **Novelty.** Not found in the sources read in this form; routine. A finite-level form of one inequality of DALAG Lemma 5.10, used in §8.4.1 for a finite union of translates.
-- source:
--   Finite-level form of one inequality of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 5.10 (§5.3.2, p. 160; Chapter 5 is by D. Roy), as used in §8.4.1 (pp. 245–247; Chapter 8 is by D. Roy); the separators are the Chinese remainder theorem. Not found in the sources read in this form; routine. Uses DiazModulus.sum_boxHilb_le_boxHilb_iInf and DiazModulus.boxHilb_map_algEquiv. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem exists_card_mul_boxHilb_le_translates {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFmono : Monotone F)
    (hFmul : ∀ {Tₑ Uₑ : B → ℕ} {aₑ bₑ : S}, aₑ ∈ F Tₑ → bₑ ∈ F Uₑ → aₑ * bₑ ∈ F (Tₑ + Uₑ))
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ))
    (hFex : ∀ sₑ : S, ∃ Tₑ, sₑ ∈ F Tₑ) {ι : Type*} [Fintype ι] (H : Ideal S)
    (σ : ι → S ≃ₐ[K] S) (hσ : ∀ i T, (F T).map (σ i).toLinearMap = F T)
    (hcop : Pairwise fun i j => H.map (σ i) ⊔ H.map (σ j) = ⊤) :
    ∃ C : B → ℕ, ∀ T, Fintype.card ι * boxHilb F H T ≤ boxHilb F (⨅ i, H.map (σ i)) (T + C) := by
  sorry

end DiazModulus
