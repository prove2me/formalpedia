-- Prove2me | Theorems.Thm_DDNNFNeg_lemma_5_5
-- name    : DDNNFNeg.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:41.486196+00:00
-- url     : https://prove2.me/theorems/05c33545-8338-424c-804c-6fc591bb53a2
-- title:
--   Lemma 5.5 — $\mathbb P[X \in R \mid X_Z = z] \le (2/3)^{\#\mathrm{free}(z)}$
-- statement:
--   In the setting of the Claim — a rectangle $R \subseteq f_G^{-1}(0)$ with respect to $(A, B)$, crossing edges $e_1, \dots, e_k$ of the same colour with pairwise disjoint neighbourhoods, $Z = V \setminus \bigcup_i e_i$ — let $X$ be the indicator vector of a uniformly random independent set of $G$. For every possible value $z$ of $X_Z$,
--   $$
--   \mathbb P[X \in R \mid X_Z = z] \le \left(\tfrac{2}{3}\right)^{\#\mathrm{free}(z)},
--   $$
--   where $\mathrm{free}(z) = \{ i \in [k] : e_i \text{ is free with respect to } z \}$.
--
--   **Formalization Note** The conditional probability is the counting ratio over the independent sets of $G$, conditioning on "$x$ agrees with $z$ on $Z$". All $z$ are allowed: for a value of probability $0$ the ratio is $0$.
--
--   Differences from the source:
--   - generalization: the setting of §5.2: G 3-regular balanced-cut expander, (A, B) balanced, k = Ω(n) → G any graph with a proper colouring, (A, B) any partition, any k; reason: the lemma does not use these hypotheses; the paper's setting is a special case
--   - encoding: P[X ∈ R | X_Z = z] for every possible value z → the counting ratio condFrac over indepSets G, for every assignment z (value 0 when the condition has probability 0); reason: the uniform law on independent sets; the extra z give the trivial bound 0 ≤ (2/3)^m
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Lemma 5.5, p.13

import Mathlib
import Definitions.Def_DDNNFNeg_fG
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring
import Definitions.Def_DDNNFNeg_IsRectangle
import Definitions.Def_DDNNFNeg_IsFree
import Definitions.Def_DDNNFNeg_indepSets
import Definitions.Def_DDNNFNeg_condFrac

namespace DDNNFNeg

/-- **Lemma 5.5** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.13): in the setting of the Claim (a rectangle `R ⊆ f_G⁻¹(0)` w.r.t.
`(A, Aᶜ)`, crossing edges `eᵢ = {uᵢ, vᵢ}` of one colour with pairwise disjoint neighbourhoods,
`Z = V \ ⋃ᵢ eᵢ`), for `X` a uniformly random independent set of `G` and every possible value `z`
of `X_Z`,
`P[X ∈ R | X_Z = z] ≤ (2/3)^{#free(z)}`, where `free(z) = {i : eᵢ is free with respect to z}`.

**Formalization Note** The conditional probability is the counting ratio `condFrac` over the
independent sets `indepSets G`, conditioning on "`x` agrees with `z` on `Z`". Every `z` is
allowed: when `X_Z = z` has probability `0` the left side is the junk value `0`. The
3-regularity, expansion and balancedness of the paper's setting are not used and not assumed
(a generalization). -/
theorem lemma_5_5 {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Sym2 (Fin n) → Fin 3) (hc : IsProperEdgeColoring G c)
    (A : Finset (Fin n)) (R : Set (Fin n → Bool)) (hR : IsRectangle A R)
    (hR0 : ∀ x ∈ R, fG G c x = false)
    (u v : Fin k → Fin n) (huA : ∀ i, u i ∈ A) (hvA : ∀ i, v i ∉ A)
    (hadj : ∀ i, G.Adj (u i) (v i)) (col : Fin 3) (hcol : ∀ i, c s(u i, v i) = col)
    (hdisj : ∀ i j, i ≠ j → Disjoint (edgeNbhd G s(u i, v i)) (edgeNbhd G s(u j, v j)))
    (z : Fin n → Bool) :
    condFrac (indepSets G) (fun x => x ∈ R)
        (fun x => ∀ t, (∀ j, t ≠ u j ∧ t ≠ v j) → x t = z t) ≤
      (2 / 3 : ℝ) ^ (Finset.univ.filter (fun i => IsFree G s(u i, v i) z)).card := by sorry

end DDNNFNeg
