-- Prove2me | Theorems.Thm_DDNNFNeg_lemma_5_5_claim
-- name    : DDNNFNeg.lemma_5_5_claim
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:04.049746+00:00
-- url     : https://prove2.me/theorems/a7243bba-1bcc-4e8d-ab65-b14010eb218f
-- title:
--   Claim in the proof of Lemma 5.5 — a free edge has an endpoint fixed to $0$ on $R$
-- statement:
--   Let $G$ be a graph on $[n]$ with a proper 3-edge-colouring, $(A, B)$ a partition of $[n]$, and $R \subseteq f_G^{-1}(0)$ a rectangle with respect to $(A, B)$. Let $e_1, \dots, e_k$, $e_i = \{u_i, v_i\}$ with $u_i \in A$, $v_i \in B$, be crossing edges of the same colour with pairwise disjoint neighbourhoods, let $Z = V \setminus \bigcup_i e_i$, and let $z$ be an assignment.
--
--   For each edge $e_i$ that is free with respect to $z$ there is an endpoint $w_i \in e_i$ such that
--   $$
--   x(w_i) = 0 \quad \text{for every independent set } x \in R \text{ consistent with } z,
--   $$
--   where $x$ is consistent with $z$ if $x(t) = z(t)$ for all $t \in Z$.
--
--   This is what bounds the conditional probability in Lemma 5.5 by $(2/3)$ per free edge.
--
--   Differences from the source:
--   - generalization: the setting of §5.2: G 3-regular balanced-cut expander, (A, B) balanced, k = Ω(n) → G any graph with a proper colouring, (A, B) any partition, any k; reason: the claim does not use these hypotheses; the paper's setting is a special case
--   - encoding: crossing edges eᵢ = {uᵢ, vᵢ}, uᵢ ∈ A, vᵢ ∈ B; z ∈ {0,1}^Z → ordered pairs (u i, v i) with u i ∈ A, v i ∉ A, adjacent in G; z a full assignment whose values on Z are used; reason: same instances
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Claim in the proof of Lemma 5.5, p.13

import Mathlib
import Definitions.Def_DDNNFNeg_fG
import Definitions.Def_DDNNFNeg_IsProperEdgeColoring
import Definitions.Def_DDNNFNeg_IsRectangle
import Definitions.Def_DDNNFNeg_IsFree
import Definitions.Def_DDNNFNeg_indepSets

namespace DDNNFNeg

/-- **Claim in the proof of Lemma 5.5** (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), p.13). Let `R ⊆ f_G⁻¹(0)` be a rectangle with
respect to the partition `(A, B)`, `B = Aᶜ`, and let `e₁, …, e_k`, `eᵢ = {uᵢ, vᵢ}` with `uᵢ ∈ A`
and `vᵢ ∈ B`, be crossing edges of the same colour with pairwise disjoint neighbourhoods; let
`Z = V \ ⋃ᵢ eᵢ` and fix an assignment `z`. Then for each edge `eᵢ` free with respect to `z`
there is an endpoint `wᵢ ∈ eᵢ` such that `x(wᵢ) = 0` for every independent set `x ∈ R`
consistent with `z` (i.e. `x(t) = z(t)` for all `t ∈ Z`).

**Formalization Note** The edges are given as ordered pairs `(u i, v i)` with `u i ∈ A`,
`v i ∉ A`, adjacent in `G`. The paper's setting (§5.2) also has `G` 3-regular, a balanced-cut
expander, `(A, B)` balanced and `k = Ω(n)`; the claim does not use these, and they are not
assumed (a generalization). The assignment `z` is a full assignment of which only the values
on `Z` matter. -/
theorem lemma_5_5_claim {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Sym2 (Fin n) → Fin 3) (hc : IsProperEdgeColoring G c)
    (A : Finset (Fin n)) (R : Set (Fin n → Bool)) (hR : IsRectangle A R)
    (hR0 : ∀ x ∈ R, fG G c x = false)
    (u v : Fin k → Fin n) (huA : ∀ i, u i ∈ A) (hvA : ∀ i, v i ∉ A)
    (hadj : ∀ i, G.Adj (u i) (v i)) (col : Fin 3) (hcol : ∀ i, c s(u i, v i) = col)
    (hdisj : ∀ i j, i ≠ j → Disjoint (edgeNbhd G s(u i, v i)) (edgeNbhd G s(u j, v j)))
    (z : Fin n → Bool) (i : Fin k) (hfree : IsFree G s(u i, v i) z) :
    ∃ w ∈ s(u i, v i), ∀ x ∈ indepSets G, x ∈ R →
      (∀ t, (∀ j, t ≠ u j ∧ t ≠ v j) → x t = z t) → x w = false := by sorry

end DDNNFNeg
