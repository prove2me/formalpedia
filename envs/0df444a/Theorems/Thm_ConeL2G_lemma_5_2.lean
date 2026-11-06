-- Prove2me | Theorems.Thm_ConeL2G_lemma_5_2
-- name    : ConeL2G.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:36.99098+00:00
-- url     : https://prove2.me/theorems/f436c8f3-a7e0-4af0-ab9f-d5834bfeb237
-- title:
--   Lemma 5.2 (corrected: $s\ge1$) — $\mathbb E_\mu[\mathbb 1\{c\notin X\}(\sum_i\Pi_{i,c}h)^2]\le(1-p^*_-)\|\sum_i\Pi_{i,c}h\|^2_\mu\le\beta_{|H|}\|\sum_i\Pi_{i,c}h\|^2_\mu$
-- statement:
--   Let $H$ be a finite graph with color lists satisfying $\ell_i\ge s+\deg_H(i)$ for every vertex $i$, where $s\ge1$ is real, and let $\mu$ be uniform on its proper list colorings. For every color $c$ and every $h\in L^2(\mu)$, writing $g=\sum_i\Pi_{i,c}h$ and $p^*_-=\big(\frac{s-1}{s}\big)^{|H|}$,
--   $$\mathbb E_\mu\big[\mathbb 1\{c\notin X\}\,g(X)^2\big]\ \le\ (1-p^*_-)\,\|g\|_\mu^2\ \le\ \beta_{|H|}\,\|g\|_\mu^2,$$
--   where $c\notin X$ means that no vertex has color $c$ and $|H|$ is the number of vertices.
--
--   The lemma controls the mass that $\sum_i\Pi_{i,c}h$ can put on colorings avoiding $c$; in Lemma 6.2 it produces the factor $\beta_d/(s-1)$.
--
--   Differences from the source:
--   - correction: no condition on s → 1 ≤ s; reason: false for 0 < s < 1: s = 1/10, H two isolated vertices, L₁ = L₂ = {a, b}, c = a, h = 1{x₁ = a} + 1{x₂ = a} satisfy every printed assumption, the left side is 1/4 and the middle −40; the paper uses the lemma only with s ≥ 5
--   - generalization: c ∈ ⋃_{i∈V(H)} L_i → any color c; reason: for c in no list every Π_{i,c} is 0 and all three expressions are 0; it specializes to the printed range of c
--   - encoding: E_µ[1{c ∉ X}(Σ_i Π_{i,c}h(X))²], |H| → innerPi µ (indicator of ∀ i, x i ≠ c) ((Σ_i Π_{i,c}h)²), Fintype.card V; reason: same quantity
--   - encoding: a subgraph H of G with the lists left after pinning G ∖ H (Section 2.1) → an arbitrary finite graph with arbitrary lists; reason: every finite graph with lists is such a pinned subgraph (take G = H), and every pinned subgraph is a finite graph with lists; same instances
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Lemma 5.2, p.16

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_ConeL2G_unifMass
import Definitions.Def_ConeL2G_projPi
import Definitions.Def_ConeL2G_beta

namespace ConeL2G

/-- **Lemma 5.2 (a disallowed color), corrected: `s ⩾ 1`.** Li–Oveis Gharan, arXiv:2610.37721,
Lemma 5.2, p.16: "For every `h ∈ L²(µ)` and any `c ∈ ⋃_{i∈V(H)} Lᵢ` where `ℓᵢ ⩾ s + deg_H(i)` for
`i ∈ H`, we have
`E_µ[1{c ∉ X}(Σᵢ Π_{i,c}h(X))²] ⩽ (1 − p*₋)‖Σᵢ Π_{i,c}h‖²_µ ⩽ β_{|H|}‖Σᵢ Π_{i,c}h‖²_µ`,
where `p*₋ := ((s−1)/s)^{|H|}`."

**Correction.** The printed lemma puts no condition on `s`; for `0 < s < 1` it is false
(`s = 1/10`, two isolated vertices with lists `{a, b}`, `c = a`, `h = 1{x₁ = a} + 1{x₂ = a}`: the
left side is `1/4`, the middle `−40`). The hypothesis `1 ⩽ s` is added; the paper uses the lemma
with `s ⩾ 5`.

**Formalization Note.** `H` is an arbitrary finite graph with lists (Section 2.1), `|H|` its number
of vertices, `µ = unifMass H L`. The hypothesis `c ∈ ⋃ Lᵢ` is dropped: otherwise every `Π_{i,c}`
is `0` and all three terms vanish. `c ∉ X` means no vertex has color `c`. -/
theorem lemma_5_2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {K : ℕ} (L : V → Finset (Fin K)) (s : ℝ) (hs : 1 ≤ s)
    (hL : ∀ i : V, s + (H.degree i : ℝ) ≤ ((L i).card : ℝ)) (c : Fin K)
    (h : (V → Fin K) → ℝ) :
    MarkovMixing.innerPi (unifMass H L) (fun x => if ∀ i, x i ≠ c then (1 : ℝ) else 0)
        (fun x => (∑ i, projPi H L i c h x) ^ 2) ≤
      (1 - ((s - 1) / s) ^ Fintype.card V) *
        MarkovMixing.innerPi (unifMass H L) (fun x => ∑ i, projPi H L i c h x)
          (fun x => ∑ i, projPi H L i c h x) ∧
    (1 - ((s - 1) / s) ^ Fintype.card V) *
        MarkovMixing.innerPi (unifMass H L) (fun x => ∑ i, projPi H L i c h x)
          (fun x => ∑ i, projPi H L i c h x) ≤
      beta s (Fintype.card V) *
        MarkovMixing.innerPi (unifMass H L) (fun x => ∑ i, projPi H L i c h x)
          (fun x => ∑ i, projPi H L i c h x) := by sorry

end ConeL2G
