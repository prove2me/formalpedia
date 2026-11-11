-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_10
-- name    : DetSpectralSparsify.Dense.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:00.080695+00:00
-- url     : https://prove2.me/theorems/bced775b-5b60-4d60-9c91-cf0d0c9b7ba1
-- title:
--   Lemma 10 (Degree regularization) — fibers, degrees Θ(d), conductance Ω(ϕ), contraction, in O((m + vol) log n) time
-- statement:
--   Fix $c_0>0$; the hypothesis $\delta=\Omega(d)$ is read as $\delta_G\ge c_0d$. There are a program and constants $c,C,c',C_t>0$ (depending only on $c_0$) such that the following holds. Let $G$ be a weighted multigraph on $n\ge2$ vertices, possibly with self-loops (of nonnegative weight), whose non-loop edges have weight in $[1,2]$, with $\Phi(G)\ge\phi$, $d\ge1$ and $\deg_G(v)\ge c_0d$ for all $v$. On input $(G,d)$ the program halts within
--   $$C_t\,(m+\mathrm{vol}_G(V))\log n$$
--   steps and outputs a weighted multigraph $G^\circ$ and a partition of $V(G^\circ)$ into fibers $(F_v)_{v\in V(G)}$ such that
--
--   1. $|V(G^\circ)|\le C(n+\mathrm{vol}_G(V)/d)$ and $|E(G^\circ)|\le C(m+\mathrm{vol}_G(V))$;
--   2. every non-loop edge of $G^\circ$ has weight in $[1,2]$, its loops have nonnegative weight, $cd\le\deg_{G^\circ}(x)\le Cd$ for every $x$, and $\deg^\#_{G^\circ}(x)\le\deg_{G^\circ}(x)$;
--   3. $\Phi(G^\circ)\ge c'\phi$;
--   4. contracting every fiber maps a $(1\pm\varepsilon)$-spectral sparsifier of $G^\circ$ to a $(1\pm\varepsilon)$-spectral sparsifier of $G$, for every $\varepsilon$.
--
--   Degree regularization is the first step of the expander sparsifier (Algorithm 6).
--
--   **Formalization Note** The fibers are given by a surjective map $f:V(G^\circ)\to V(G)$ (`decodeRegularized`); contraction deletes the self-loops it creates. "$\deg^\#\le\deg=O(d)$" is the conjunction of the last two parts of (ii).
--
--   Differences from the source:
--   - reading: a deterministic algorithm running in the stated time (the paper fixes no machine model) → a fixed program of the closed real RAM `Program` (natural +, truncated −; real + − × ÷ √, ℕ→ℝ cast, comparisons; no floor, real constants or oracles) halting within the stated number of steps, with natural words of O(log(input + T)) bits, input and output in the layouts `graphInput`/`decodeGraph`; reason: the paper names no model; arithmetic complexity on real weights is the natural reading, and the closed instruction set prevents a step from hiding unbounded work
--   - reading: δ = Ω(d) → for every c₀ > 0 the hypothesis δ ≥ c₀ d, with the program and all constants depending on c₀ only; reason: Ω in a hypothesis: the conclusion's constants may depend on the hidden constant; the statement covers every value of it
--   - reading: weighted multigraph, possibly with self-loops → self-loops of nonnegative weight; reason: cluster graphs G⟨U⟩, to which the lemma is applied, carry loops of weight deg_G(v) − deg_{G[U]}(v) ≥ 0
--   - encoding: n-vertex graph (bounds contain log n) → hypothesis 2 ≤ n; reason: at n = 1 we have log n = 0 and the O-bounds degenerate to 0; a one-vertex graph has zero Laplacian and nothing to sparsify
--   - encoding: a partition of V(G°) into fibers (F_v)_{v ∈ V(G)} → a surjective map f : V(G°) → V(G), F_v = f⁻¹(v); reason: a partition indexed by V(G) with nonempty parts
--   - generalization: (iv) maps a spectral sparsifier of G° to one of G → for every real ε and every multigraph H on V(G°) with arbitrary real weights satisfying the (1 ± ε) sandwich; reason: the contraction identity QᵀL_{H°}Q = L_H holds for all weights; spectral sparsifiers are a special case
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.18, Lemma 10 (with Algorithm 4)

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 10 (Degree regularization), p.18. For every `c₀ > 0` (the hypothesis `δ = Ω(d)` read as
`δ ≥ c₀ d`) there are a program and constants such that for every weighted multigraph `G` whose
non-loop weights lie in `[1, 2]`, with `Φ(G) ≥ ϕ`, `d ≥ 1` and minimum degree `δ ≥ c₀ d`, the
program builds in `O((m + vol_G(V)) log n)` steps a multigraph `G°` and a partition of its vertices
into fibers `(F_v)_{v ∈ V(G)}` with (i)–(iv). -/
theorem lemma_10 :
    ∀ c₀ : ℝ, 0 < c₀ →
    ∃ (P : Program) (K : ℕ) (c C c' Ct : ℝ), 0 < c ∧ 0 < C ∧ 0 < c' ∧ 0 < Ct ∧
    ∀ (n : ℕ) (G : Multigraph n) (d ϕ : ℝ),
      2 ≤ n → G.NonloopWeightsIn 1 2 → G.LoopsNonneg → G.CondAtLeast ϕ → 1 ≤ d →
      (∀ v, c₀ * d ≤ G.deg v) →
      ∃ (T : ℕ) (s' : State), RunsWithin P K (2 + n + G.m) (graphInput G [] [d]) T s' ∧
      ∃ (N : ℕ) (G' : Multigraph N) (f : Fin N → Fin n),
        decodeRegularized n s' = some ⟨N, G', f⟩ ∧
        Function.Surjective f ∧
        -- (i)
        (N : ℝ) ≤ C * (n + G.vol Finset.univ / d) ∧
        (G'.m : ℝ) ≤ C * (G.m + G.vol Finset.univ) ∧
        -- (ii)
        G'.NonloopWeightsIn 1 2 ∧ G'.LoopsNonneg ∧
        (∀ x, c * d ≤ G'.deg x ∧ G'.deg x ≤ C * d) ∧
        (∀ x, (G'.combDeg x : ℝ) ≤ G'.deg x) ∧
        -- (iii)
        G'.CondAtLeast (c' * ϕ) ∧
        -- (iv)
        (∀ (ε : ℝ) (H : Multigraph N), IsSpectralSparsifier ε G' H →
          IsSpectralSparsifier ε G (Multigraph.contract f H)) ∧
        -- running time
        (T : ℝ) ≤ Ct * (G.m + G.vol Finset.univ) * Real.log n := by sorry

end DetSpectralSparsify.Dense
