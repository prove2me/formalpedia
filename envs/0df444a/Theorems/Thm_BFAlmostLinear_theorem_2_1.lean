-- Prove2me | Theorems.Thm_BFAlmostLinear_theorem_2_1
-- name    : BFAlmostLinear.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:26.582377+00:00
-- url     : https://prove2.me/theorems/8ad0e3d4-1774-4d95-8b35-a09c02c8ec35
-- title:
--   Theorem 2.1 — betweenness reduction: $\sum_{r\in N}\min\{|V^{\mathrm{in}}_r|,|V^{\mathrm{out}}_r|\}\le\tilde O(nb)$ whp
-- statement:
--   Let $G$ be a weighted graph on $n$ vertices with frozen flags, $N$ a set of vertices, $b\ge1$ and hop bounds $h_1,h_2$. Let $U\subseteq N$ contain each vertex of $N$ independently with probability $1/b$. There is an absolute exponent $a$, and for every $c>0$ a constant $K$, such that with probability at least $1-n^{-c}$ over $U$: for every potential $\phi$ that fixes $U$ and all families $V^{\mathrm{in}}_r,V^{\mathrm{out}}_r\subseteq V$ ($r\in N$) with $d^{h_1}_\phi(s,r)+d^{h_2}_\phi(r,t)<0$ whenever $s\in V^{\mathrm{in}}_r$, $t\in V^{\mathrm{out}}_r$,
--   $$\sum_{r\in N}\min\{|V^{\mathrm{in}}_r|,|V^{\mathrm{out}}_r|\}\le K\,n\,b\,(\log n)^a.$$
--
--   This is the first of the paper's two new tools: after a reweighting that fixes a random sample, the forward and backward searches have almost linear total size.
--
--   Differences from the source:
--   - generalization: one hop bound $h$ → a pair $(h_1,h_2)$; reason: Lemma 4.6's proof (p.18) applies the result to $d^0+d^1$; $h_1=h_2=h$ is the printed form.
--   - generalization: $N$ the negative vertices → any set of vertices; reason: the proof only uses the sampling of $U$ from $N$.
--   - encoding: $\tilde O(nb)$ → $K\,n\,b\,(\log n)^a$ with $a$ absolute and $K$ depending on $c$; reason: footnote 1, p.1.
--   - encoding: "with high probability" → probability $\ge1-n^{-c}$ for every $c>0$; reason: footnote 2, p.1.
--   - encoding: frozen-flag convention → hypothesis `Frozen`; reason: §1.1, p.2.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Theorem 2.1, p.5

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph
import Definitions.Def_BFAlmostLinear_sampleMass

namespace BFAlmostLinear

open Classical in
/-- **Theorem 2.1**, p.5. "Let U ⊆ N be a random sample where each vertex in N is sampled with probability 1/b. With
high probability over the randomness of U, the following holds. Consider any potential function ϕ that fixes U, and
for each negative vertex r ∈ N, consider any V^in_r, V^out_r ⊆ V such that for all s ∈ V^in_r, t ∈ V^out_r, we have
d^h_ϕ(s, r) + d^h_ϕ(r, t) < 0. Then, Σ_{r∈N} min{|V^in_r|, |V^out_r|} ≤ Õ(nb)."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Theorem 2.1, p.5.

**Formalization Note.** `Õ(nb)` is `K n b (log n)^a`, where the exponent `a` is absolute and `K` depends on the
probability exponent `c`. Generalized to a hop pair `(h₁, h₂)`, with `N` any set of vertices (finding F5 of the plan:
Lemma 4.6's proof needs `h₁ ≠ h₂`). The families `V^in`, `V^out` are quantified inside the good event. -/
theorem theorem_2_1 :
    ∃ a : ℕ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V) (b : ℝ) (h₁ h₂ : ℕ),
        G.Frozen → 1 ≤ b →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤
          goodMass N b fun U =>
            ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ → ∀ Vin Vout : V → Finset V,
              (∀ r ∈ N, ∀ s ∈ Vin r, ∀ t ∈ Vout r, G.InX h₁ h₂ ϕ s r t) →
              ((∑ r ∈ N, min (Vin r).card (Vout r).card : ℕ) : ℝ) ≤
                K * (Fintype.card V : ℝ) * b * Real.log (Fintype.card V) ^ a := by sorry

end BFAlmostLinear
