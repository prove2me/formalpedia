-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_theorem_19
-- name    : DetSpectralSparsify.Dense.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:29.765751+00:00
-- url     : https://prove2.me/theorems/f8614877-5ea8-4718-bdb8-09bceb1802f2
-- title:
--   Theorem 19 (Deterministic sparsification) — (1±ε)-sparsifier with Õ(n(b+log²n)ε⁻²) edges in m^{1+o(1)} + Õ(n²(b+log²n)ε^{−9/2}) time
-- statement:
--   There are a deterministic program, a sequence $\phi_n$ with $\phi_n^{-1}=\log^{9+h(n)}n$ where $h(n)\to0$, and a function $g(m)\to0$, such that for every $c$ there is a constant $C$ with the following property. Let $G$ be a positively weighted $n$-vertex, $m$-edge multigraph ($n\ge2$) and
--   $$b:=1+\Big\lceil\log_2\frac{w_{\max}}{w_{\min}}\Big\rceil .$$
--   Let $0<\varepsilon\le1/2$ and suppose $m,\varepsilon^{-1}\le n^c$. On input $(G,\varepsilon)$ the program halts and outputs a reweighted subgraph $H$ of $G$ that is a $(1\pm\varepsilon)$-spectral sparsifier,
--   $$(1-\varepsilon)L_G\preceq L_H\preceq(1+\varepsilon)L_G,$$
--   with
--   $$|E(H)|\le C\,n(b+\log^2n)\,\phi_n^{-2}\varepsilon^{-2}\log^4n\tag{47}$$
--   edges, after at most
--   $$m^{1+g(m)}+C\,n^2(b+\log^2n)\,\phi_n^{-5}\varepsilon^{-9/2}\log^{19/2}n\tag{48}$$
--   steps. Since $\phi_n^{-1}=\log^{9+h(n)}n$, these bounds are
--   $$|E(H)|\le C\,n(b+\log^2n)\,\varepsilon^{-2}\log^{22+2h(n)}n\tag{49}$$
--   edges and
--   $$m^{1+g(m)}+C\,n^2(b+\log^2n)\,\varepsilon^{-9/2}\log^{109/2+5h(n)}n\tag{50}$$
--   steps.
--
--   This is the paper's main result: a deterministic spectral sparsifier of near-optimal size whose vertex-dependent work is near-quadratic, independent of the matrix multiplication exponent. For polynomially bounded weight ratios ($b=O(\log n)$) it gives the abstract's $\log^{24+o(1)}$ and $\log^{113/2+o(1)}$ bounds.
--
--   **Formalization Note** Input $(G,\varepsilon)$ in `graphInput G [] [ε]` on the real RAM of `Machine`, output by `decodeGraph`. $b$ is `bClasses` (extrema over all edges including self-loops; $b=1$ for an empty edge list). $\log$ is the natural logarithm. The program, $\phi$, $h$, $g$ and the word-size exponent are fixed first, then $c$, then $C$.
--
--   Differences from the source:
--   - reading: a deterministic algorithm running in the stated time (the paper fixes no machine model) → a fixed program of the closed real RAM `Program` (natural +, truncated −; real + − × ÷ √, ℕ→ℝ cast, comparisons; no floor, real constants or oracles) halting within the stated number of steps, with natural words of O(log(input + T)) bits, input and output in the layouts `graphInput`/`decodeGraph`; reason: the paper names no model; arithmetic complexity on real weights is the natural reading, and the closed instruction set prevents a step from hiding unbounded work
--   - encoding: ϕ_n := log^{−9−o(1)} n → a sequence ϕ : ℕ → (0,1] and h → 0 with ϕ(n)⁻¹ = (log n)^{9+h(n)} for n ≥ 3 (`IsPhiSequence`), chosen before the instances; reason: spells out the o(1); ϕ cannot be an arbitrarily small free parameter
--   - encoding: O(·), m^{1+o(1)} and m, ε⁻¹ ≤ n^{O(1)} → the program and the functions g → 0 (steps ≤ m^{1+g(m)} + …) are fixed first; then for every c ∈ ℕ there is C > 0 such that every instance with m ≤ n^c and ε⁻¹ ≤ n^c meets the bounds with constant C; the o(1) of (49), (50) is 2h(n), 5h(n); reason: standard quantifier order for these asymptotic claims: constants are uniform over graphs, weights and accuracies
--   - generalization: standing assumption ε⁻¹ ≤ n in every theorem that produces a spectral sparsifier (p.5), plus ε⁻¹ ≤ n^{O(1)} → only ε⁻¹ ≤ n^c is assumed; reason: covers every source instance; for ε⁻¹ > n the source itself notes that the whole graph after aggregating parallel edges (at most n² edges) suffices, which fits the stated bounds
--   - generalization: standing convention 'we discard isolated vertices' (p.5); the proof's first step discards them → G may have isolated vertices; n counts them; reason: every source instance is covered, and the bounds only grow with n
--   - reading: a (1 ± ε)-spectral sparsifier: a weighted graph H on V(G) with (1−ε)L_G ⪯ L_H ⪯ (1+ε)L_G (Definition 2) → H additionally is a reweighted subgraph of G: each edge of H has positive weight and joins two distinct vertices joined by a non-loop edge of G (`IsReweightedSubgraph`); reason: the abstract and p.1 describe the output as a reweighted subgraph; the stronger reading is the one the algorithm delivers (every recursive output is supported on its input)
--   - encoding: n-vertex graph (bounds contain log n) → hypothesis 2 ≤ n; reason: at n = 1 we have log n = 0 and the O-bounds degenerate to 0; a one-vertex graph has zero Laplacian and nothing to sparsify
--   - encoding: b := 1 + ⌈log₂(w_max/w_min)⌉ → extrema over all edges of G (self-loops included); b = 1 for an empty edge list; reason: the formula is undefined for an empty edge list
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, pp.31–32, Theorem 19, (47)–(50)

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Theorem 19 (Deterministic sparsification), pp.31–32. There are a deterministic program, a
sequence `ϕ_n` with `ϕ_n⁻¹ = log^{9+h(n)} n`, `h → 0`, and `g → 0` such that for every `c` there is
`C`: for every positively weighted `n`-vertex, `m`-edge multigraph `G` (`n ≥ 2`) with
`b = 1 + ⌈log₂(w_max/w_min)⌉`, every `0 < ε ≤ 1/2`, and `m, ε⁻¹ ≤ n^c`, the program halts on
`(G, ε)` and outputs a reweighted subgraph `H` of `G` that is a `(1 ± ε)`-spectral sparsifier of
`G`, with `|E(H)| ≤ C n (b + log² n) ϕ_n⁻² ε⁻² log⁴ n` (47) after
`m^{1+g(m)} + C n² (b + log² n) ϕ_n⁻⁵ ε^{-9/2} log^{19/2} n` steps (48); equivalently
`|E(H)| ≤ C n (b + log² n) ε⁻² log^{22+2h(n)} n` (49) and
`m^{1+g(m)} + C n² (b + log² n) ε^{-9/2} log^{109/2+5h(n)} n` steps (50). -/
theorem theorem_19 :
    ∃ (P : Program) (K : ℕ) (ϕ h g : ℕ → ℝ), IsPhiSequence ϕ h ∧ Vanishing g ∧
    ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : Multigraph n) (ε : ℝ),
      2 ≤ n → G.PosWeights → 0 < ε → ε ≤ 1 / 2 →
      (G.m : ℝ) ≤ (n : ℝ) ^ c → ε⁻¹ ≤ (n : ℝ) ^ c →
      ∃ (T : ℕ) (s' : State) (H : Multigraph n),
        RunsWithin P K (2 + n + G.m) (graphInput G [] [ε]) T s' ∧
        decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
        let b : ℝ := G.bClasses
        let L : ℝ := Real.log n
        -- (47)
        (H.m : ℝ) ≤ C * n * (b + L ^ 2) * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ * L ^ 4 ∧
        -- (48)
        (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
          C * (n : ℝ) ^ 2 * (b + L ^ 2) * (ϕ n)⁻¹ ^ 5 * ε ^ (-(9 / 2 : ℝ)) * L ^ (19 / 2 : ℝ) ∧
        -- (49)
        (H.m : ℝ) ≤ C * n * (b + L ^ 2) * (ε ^ 2)⁻¹ * L ^ (22 + 2 * h n) ∧
        -- (50)
        (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
          C * (n : ℝ) ^ 2 * (b + L ^ 2) * ε ^ (-(9 / 2 : ℝ)) * L ^ (109 / 2 + 5 * h n) := by sorry

end DetSpectralSparsify.Dense
