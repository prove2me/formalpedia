-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_theorem_13
-- name    : DetSpectralSparsify.Dense.theorem_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:59.570259+00:00
-- url     : https://prove2.me/theorems/6bd4598d-5b5c-4836-b7b8-d90837e192eb
-- title:
--   Theorem 13 (Deterministic expander decomposition) — m^{1+o(1)} time, ≤ m/2 crossing edges, cluster conductance ϕ_n
-- statement:
--   There are a deterministic program, a sequence $\phi_n=\log^{-9-o(1)}n$ and a function $g(m)\to0$ such that for every unweighted multigraph $G$ with $n$ vertices, $m$ edges and no isolated vertex, the program halts within $(m+1)^{1+g(m)}$ steps (the paper's $m^{1+o(1)}$) and outputs a partition
--   $$V(G)=V_1\,\dot\cup\,\cdots\,\dot\cup\,V_t$$
--   such that at most $m/2$ edges have endpoints in distinct clusters and, for every $i$, the cluster graph $G\langle V_i\rangle$ has conductance at least $\phi_n$.
--
--   Applied to the unweighted residual graph, the decomposition exposes high-conductance clusters to be sparsified (Algorithm 7). The paper derives it from [Chu23, Theorem 2.10].
--
--   **Formalization Note** The output is the cluster index of every vertex $v$ in natural cell $1+v$ and $t$ in natural cell $0$; every label below $t$ must occur. "Unweighted" means all weights equal $1$; the loops of $G\langle V_i\rangle$ then have weight $\deg_G(v)-\deg_{G[V_i]}(v)$. Cluster graphs keep the other vertices isolated, which does not change the all-cuts conductance condition.
--
--   Differences from the source:
--   - reading: a deterministic algorithm running in the stated time (the paper fixes no machine model) → a fixed program of the closed real RAM `Program` (natural +, truncated −; real + − × ÷ √, ℕ→ℝ cast, comparisons; no floor, real constants or oracles) halting within the stated number of steps, with natural words of O(log(input + T)) bits, input and output in the layouts `graphInput`/`decodeGraph`; reason: the paper names no model; arithmetic complexity on real weights is the natural reading, and the closed instruction set prevents a step from hiding unbounded work
--   - encoding: ϕ_n := log^{−9−o(1)} n → a sequence ϕ : ℕ → (0,1] and h → 0 with ϕ(n)⁻¹ = (log n)^{9+h(n)} for n ≥ 3 (`IsPhiSequence`), chosen before the instances; reason: spells out the o(1); ϕ cannot be an arbitrarily small free parameter
--   - encoding: m^{1+o(1)} time → at most (m+1)^{1+g(m)} steps with g → 0 fixed with the program; reason: spells out the o(1); for m ≥ 2 the two bounds are interchangeable (absorb log((m+1)/m)/log m into g); at m = 1 the printed m^{1+g(m)} = 1 would force every program to halt after one step on a one-edge input, which no program that also handles large inputs can do, so the asymptotic claim is read with base m + 1
--   - encoding: standing convention 'we discard isolated vertices' (§2, p.5) → hypothesis `G.NoIsolated` (every vertex is an endpoint of some edge); reason: the section's standing assumption made explicit as a binder; it excludes no instance the source considers
--   - encoding: unweighted graph G (a multigraph by §2) → a `Multigraph` with all weights 1 (loops and parallel edges allowed); reason: the standing scope 'all graphs are finite undirected weighted multigraphs' (p.4)
--   - encoding: G⟨V_i⟩ has conductance at least ϕ_n → `CondAtLeast (G.cluster V_i) (ϕ n)` on the full vertex set, the other vertices being isolated; reason: isolated vertices of degree 0 do not change the all-cuts condition, which is vacuous for singleton clusters
--   - encoding: a partition V(G) = V₁ ∪̇ ⋯ ∪̇ V_t → every vertex has a label below t and every label below t occurs at some vertex; reason: the label function makes the clusters disjoint and exhaustive; surjectivity ensures every listed cluster is nonempty
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.22, Theorem 13 (from Chuzhoy 2023, Theorem 2.10)

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Theorem 13 (Deterministic expander decomposition), p.22 ([Chu23, Theorem 2.10]). There is a
deterministic program running in `(m+1)^{1+o(1)}` steps (the paper's `m^{1+o(1)}`) that, given an `n`-vertex, `m`-edge unweighted multigraph
`G`, outputs a partition `V(G) = V_1 ∪ ⋯ ∪ V_t` (vertex `v` is in cluster `nat[1+v]`, `t = nat[0]`)
such that at most `m/2` edges have endpoints in distinct clusters and every cluster graph
`G⟨V_i⟩` has conductance at least `ϕ_n = log^{-9-o(1)} n`. -/
theorem theorem_13 :
    ∃ (P : Program) (K : ℕ) (ϕ h g : ℕ → ℝ), IsPhiSequence ϕ h ∧ Vanishing g ∧
    ∀ (n : ℕ) (G : Multigraph n), G.Unweighted → G.NoIsolated →
      ∃ (T : ℕ) (s' : State), RunsWithin P K (2 + n + G.m) (graphInput G [] []) T s' ∧
        (∀ v : Fin n, s'.nat (1 + v.val) < s'.nat 0) ∧
        (∀ i < s'.nat 0, ∃ v : Fin n, s'.nat (1 + v.val) = i) ∧
        2 * (Finset.univ.filter fun e : Fin G.m =>
            s'.nat (1 + (G.src e).val) ≠ s'.nat (1 + (G.dst e).val)).card ≤ G.m ∧
        (∀ i < s'.nat 0,
          (G.cluster (Finset.univ.filter fun v : Fin n => s'.nat (1 + v.val) = i)).CondAtLeast
            (ϕ n)) ∧
        (T : ℝ) ≤ ((G.m : ℝ) + 1) ^ (1 + g G.m) := by sorry

end DetSpectralSparsify.Dense
