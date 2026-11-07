-- Prove2me | Theorems.Thm_BFAlmostLinear_corollary_2_8
-- name    : BFAlmostLinear.corollary_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:27.852479+00:00
-- url     : https://prove2.me/theorems/a6c0b5be-aec6-40ad-b129-05720bc1e166
-- title:
--   Corollary 2.8 — weighted betweenness reduction: $\le\tilde O(\Lambda b)$ whp
-- statement:
--   Let $G$ be a weighted graph on $n$ vertices with frozen flags, $N$ a set of vertices, $b\ge1$, hop bounds $h_1,h_2$, and $\lambda:V\to[0,\infty)$ with total weight $\Lambda=\sum_v\lambda(v)$. Let $U\subseteq N$ contain each vertex of $N$ independently with probability $1/b$. There is an absolute exponent $a$, and for every $c>0$ a constant $K$, such that with probability at least $1-n^{-c}$ over $U$: for every potential $\phi$ that fixes $U$ and all families $V^{\mathrm{in}}_r,V^{\mathrm{out}}_r$ with $d^{h_1}_\phi(s,r)+d^{h_2}_\phi(r,t)<0$ for $s\in V^{\mathrm{in}}_r$, $t\in V^{\mathrm{out}}_r$,
--   $$\sum_{r\in N}\min\Big\{\sum_{v\in V^{\mathrm{in}}_r}\lambda(v),\ \sum_{v\in V^{\mathrm{out}}_r}\lambda(v)\Big\}\le K\,\Lambda\,b\,(\log n)^a.$$
--
--   The vertex weights let the searches of §4.2 charge their cost to degrees and counters.
--
--   Differences from the source:
--   - generalization: one hop bound $h$ → a pair $(h_1,h_2)$; reason: Lemma 4.6's proof (p.18) applies this corollary to $d^0+d^1$.
--   - generalization: $N$ the negative vertices → any set of vertices; reason: the proof only uses the sampling of $U$ from $N$.
--   - encoding: $\tilde O(\Lambda b)$, "with high probability" → $K\Lambda b(\log n)^a$ with probability $\ge1-n^{-c}$; reason: footnotes 1–2, p.1.
--   - encoding: frozen-flag convention → hypothesis `Frozen`; reason: §1.1, p.2.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Corollary 2.8, p.10

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph
import Definitions.Def_BFAlmostLinear_sampleMass

namespace BFAlmostLinear

open Classical in
/-- **Corollary 2.8**, p.10. "Consider a non-negative weight λ(v) on every vertex v in the graph. Let
Λ = Σ_{v∈V} λ(v) denote the total weight. Let U ⊆ N be a random sample where each vertex in N is sampled with
probability 1/b. With high probability over the randomness of U, the following holds. Consider any potential function
ϕ that fixes U, and for each negative vertex r ∈ N, consider any V^in_r, V^out_r ⊆ V such that for all s ∈ V^in_r,
t ∈ V^out_r, we have d^h_ϕ(s, r) + d^h_ϕ(r, t) < 0. Then, Σ_{r∈N} min{Σ_{v∈V^in_r} λ(v), Σ_{v∈V^out_r} λ(v)} ≤ Õ(Λb)."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Corollary 2.8, p.10.

**Formalization Note.** `λ` comes before `U`: the proof's auxiliary graph depends on it, and the good event may depend
on it, as printed. `Õ(Λb)` is `K Λ b (log n)^a`, as in Theorem 2.1. `Λ = 0` is included. Generalized to `(h₁, h₂)`, with
`N` any set of vertices. -/
theorem corollary_2_8 :
    ∃ a : ℕ, ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] (G : WGraph V E) (N : Finset V) (b : ℝ) (h₁ h₂ : ℕ)
        (lam : V → ℝ),
        G.Frozen → 1 ≤ b → (∀ v, 0 ≤ lam v) →
        1 - (Fintype.card V : ℝ) ^ (-c) ≤
          goodMass N b fun U =>
            ∀ ϕ : V → ℝ, G.Fixes h₁ h₂ U ϕ → ∀ Vin Vout : V → Finset V,
              (∀ r ∈ N, ∀ s ∈ Vin r, ∀ t ∈ Vout r, G.InX h₁ h₂ ϕ s r t) →
              ∑ r ∈ N, min (∑ v ∈ Vin r, lam v) (∑ v ∈ Vout r, lam v) ≤
                K * (∑ v, lam v) * b * Real.log (Fintype.card V) ^ a := by sorry

end BFAlmostLinear
