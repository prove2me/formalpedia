-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_theorem_15
-- name    : DetSpectralSparsify.Dense.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:08.336094+00:00
-- url     : https://prove2.me/theorems/a1948848-82f9-4af9-8130-91d23bc6fa75
-- title:
--   Theorem 15 (Deterministic sparsification of weighted graphs) — (37)–(39) and the aggregation paragraph
-- statement:
--   There are a sequence $\phi_n=\log^{-9-o(1)}n$ and a function $g\to0$, a sparse program and, for every achievable exponent $\alpha>2$, a dense program, such that for every $c$ there is $C$ with: for every $n$-vertex, $m$-edge positively weighted multigraph $G$ ($n\ge2$, no isolated vertex) with $b:=b(G)$, every $0<\varepsilon\le1/2$ with $m,\varepsilon^{-1}\le n^c$, the program constructs a $(1\pm\varepsilon)$-spectral sparsifier $H$ of $G$ (a reweighted subgraph) with
--   $$|E(H)|\le C\,n\,b\,\phi_n^{-2}\varepsilon^{-2}\log^2n\tag{37}$$
--   edges, within
--   $$m^{1+g(m)}+C(n^{\alpha}b\log^3n+m\log n)\,\phi_n^{-2}\varepsilon^{-2}\tag{38}$$
--   steps (dense) or
--   $$m^{1+g(m)}+C\,nm\,\phi_n^{-3}\varepsilon^{-5/2}\log^3n\tag{39}$$
--   steps (sparse).
--
--   Parallel edges may be aggregated first: if the aggregated graph $\bar G$ has $\bar m$ edges and $\bar b$ occupied dyadic classes, there are dense and sparse programs with the same conclusions with $m,b$ replaced by $\bar m,\bar b$, plus an initial $O(m)$ cost. Moreover, for every positively weighted $G$, $\bar m\le\min\{m,\binom n2\}$ (self-loops deleted) and
--   $$\bar b\le b+\lceil\log_2m\rceil+1 .$$
--
--   This weighted sparsifier is used at level $0$ and at every level of the recursive algorithm.
--
--   **Formalization Note** Input $(G,\varepsilon)$ in `graphInput G [] [ε]`, output by `decodeGraph`; $\bar G$ is `G.aggregate`, $b$ is `bClasses` (extrema over all edges, $1$ for an empty edge list), and $\bar b$ is `G.aggregate.dyadicClassCount`. The exact aggregate edge cap is `n.choose 2`.
--
--   Differences from the source:
--   - reading: a deterministic algorithm running in the stated time (the paper fixes no machine model) → a fixed program of the closed real RAM `Program` (natural +, truncated −; real + − × ÷ √, ℕ→ℝ cast, comparisons; no floor, real constants or oracles) halting within the stated number of steps, with natural words of O(log(input + T)) bits, input and output in the layouts `graphInput`/`decodeGraph`; reason: the paper names no model; arithmetic complexity on real weights is the natural reading, and the closed instruction set prevents a step from hiding unbounded work
--   - reading: dense time with the factor n^ω, ω the infimum of matrix multiplication exponents (p.5) → for every α > 2 with `Achievable α` (some program multiplies n×n real matrices in C(n+1)^α steps) there is a dense program whose bound has n^α; reason: ω need not be attained; the bound is meaningful for exponents actually achieved by an algorithm, and holds for every one of them; α > 2 is the explicit reading prescribed by the BRIEF, allowing lower-degree polylogarithmic work to be absorbed in n^α
--   - encoding: ϕ_n := log^{−9−o(1)} n → a sequence ϕ : ℕ → (0,1] and h → 0 with ϕ(n)⁻¹ = (log n)^{9+h(n)} for n ≥ 3 (`IsPhiSequence`), chosen before the instances; reason: spells out the o(1); ϕ cannot be an arbitrarily small free parameter
--   - encoding: O(·), m^{1+o(1)} and m, ε⁻¹ ≤ n^{O(1)} → the program and the functions g → 0 (steps ≤ m^{1+g(m)} + …) are fixed first; then for every c ∈ ℕ there is C > 0 such that every instance with m ≤ n^c and ε⁻¹ ≤ n^c meets the bounds with constant C; reason: standard quantifier order for these asymptotic claims: constants are uniform over graphs, weights and accuracies
--   - generalization: standing assumption ε⁻¹ ≤ n in every theorem that produces a spectral sparsifier (p.5), plus ε⁻¹ ≤ n^{O(1)} → only ε⁻¹ ≤ n^c is assumed; reason: covers every source instance; for ε⁻¹ > n the source itself notes that the whole graph after aggregating parallel edges (at most n² edges) suffices, which fits the stated bounds
--   - reading: a (1 ± ε)-spectral sparsifier: a weighted graph H on V(G) with (1−ε)L_G ⪯ L_H ⪯ (1+ε)L_G (Definition 2) → H additionally is a reweighted subgraph of G: each edge of H has positive weight and joins two distinct vertices joined by a non-loop edge of G (`IsReweightedSubgraph`); reason: the abstract and p.1 describe the output as a reweighted subgraph; the stronger reading is the one the algorithm delivers (every recursive output is supported on its input)
--   - encoding: n-vertex graph (bounds contain log n) → hypothesis 2 ≤ n; reason: at n = 1 we have log n = 0 and the O-bounds degenerate to 0; a one-vertex graph has zero Laplacian and nothing to sparsify
--   - encoding: standing convention 'we discard isolated vertices' (§2, p.5) → hypothesis `G.NoIsolated` (every vertex is an endpoint of some edge); reason: the section's standing assumption made explicit as a binder; it excludes no instance the source considers
--   - encoding: b̄ occupied dyadic weight classes of the aggregated graph → G.aggregate.dyadicClassCount, the cardinality of the set of floor(log₂ w) over aggregated non-loop edges; reason: counts only nonempty classes, as in the aggregation paragraph; does not replace the count by the larger weight span b(Ḡ)
--   - reading: parallel edges may be aggregated before running the algorithm; the same conclusions hold with m, b replaced by m̄, b̄, together with an initial O(m) aggregation cost → separate dense and sparse programs with the bounds (37)–(39) in m̄, b̄ plus C·m steps; reason: the paragraph describes a variant of the algorithm; both variants are asserted
--   - encoding: b := 1 + ⌈log₂(w_max/w_min)⌉ → extrema over all edges of G; b = 1 for an empty edge list; reason: the formula is undefined for an empty edge list
--   - encoding: m̄ ≤ min{m, binom(n,2)} after self-loops are deleted → G.aggregate.m ≤ min G.m (n.choose 2); reason: the rendered PDF uses the binomial coefficient; the vertically stacked n and 2 are not the power n²
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.27, Theorem 15 (with Algorithm 8); b(G) defined on p.26

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Theorem 15 (Deterministic sparsification of weighted graphs), p.27. For an `n`-vertex,
`m`-edge positively weighted multigraph with `b = b(G)`, `0 < ε ≤ 1/2` and `m, ε⁻¹ ≤ n^{O(1)}`,
a deterministic program constructs a `(1 ± ε)`-spectral sparsifier with
`O(n b ϕ_n⁻² ε⁻² log² n)` edges (37); the sparse implementation runs in
`m^{1+o(1)} + O(n m ϕ_n⁻³ ε^{-5/2} log³ n)` time (39), and for every achievable exponent `α > 2` the
dense implementation in `m^{1+o(1)} + O((n^α b log³ n + m log n) ϕ_n⁻² ε⁻²)` time (38). After
aggregating parallel edges (giving `m̄` edges and `b̄` occupied dyadic classes), the same conclusions hold with
`m, b` replaced by `m̄, b̄` plus an initial `O(m)` cost; moreover `m̄ ≤ min{m, n.choose 2}` and
`b̄ ≤ b + ⌈log₂ m⌉ + 1`. -/
theorem theorem_15 :
    ∃ (ϕ h g : ℕ → ℝ), IsPhiSequence ϕ h ∧ Vanishing g ∧
    -- sparse implementation, (37) and (39)
    (∃ (P : Program) (K : ℕ), ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (ε : ℝ),
        2 ≤ n → G.NoIsolated → G.PosWeights →
        0 < ε → ε ≤ 1 / 2 → (G.m : ℝ) ≤ (n : ℝ) ^ c → ε⁻¹ ≤ (n : ℝ) ^ c →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m) (graphInput G [] [ε]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          -- (37)
          (H.m : ℝ) ≤ C * n * G.bClasses * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ * Real.log n ^ 2 ∧
          (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
            C * n * G.m * (ϕ n)⁻¹ ^ 3 * ε ^ (-(5 / 2 : ℝ)) * Real.log n ^ 3) ∧
    -- dense implementation, (37) and (38)
    (∀ α : ℝ, 2 < α → Achievable α →
    ∃ (P : Program) (K : ℕ), ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (ε : ℝ),
        2 ≤ n → G.NoIsolated → G.PosWeights →
        0 < ε → ε ≤ 1 / 2 → (G.m : ℝ) ≤ (n : ℝ) ^ c → ε⁻¹ ≤ (n : ℝ) ^ c →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m) (graphInput G [] [ε]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          -- (37)
          (H.m : ℝ) ≤ C * n * G.bClasses * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ * Real.log n ^ 2 ∧
          (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
            C * ((n : ℝ) ^ α * G.bClasses * Real.log n ^ 3 + G.m * Real.log n) *
              (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹) ∧
    -- sparse implementation after aggregation: m, b replaced by m̄, b̄, plus O(m)
    (∃ (P : Program) (K : ℕ), ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (ε : ℝ),
        2 ≤ n → G.NoIsolated → G.PosWeights →
        0 < ε → ε ≤ 1 / 2 → (G.m : ℝ) ≤ (n : ℝ) ^ c → ε⁻¹ ≤ (n : ℝ) ^ c →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m) (graphInput G [] [ε]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          -- (37) with b replaced by b̄
          (H.m : ℝ) ≤ C * n * G.aggregate.dyadicClassCount * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ * Real.log n ^ 2 ∧
          (T : ℝ) ≤ C * G.m + (G.aggregate.m : ℝ) ^ (1 + g G.aggregate.m) +
            C * n * G.aggregate.m * (ϕ n)⁻¹ ^ 3 * ε ^ (-(5 / 2 : ℝ)) * Real.log n ^ 3) ∧
    -- dense implementation after aggregation
    (∀ α : ℝ, 2 < α → Achievable α →
    ∃ (P : Program) (K : ℕ), ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (ε : ℝ),
        2 ≤ n → G.NoIsolated → G.PosWeights →
        0 < ε → ε ≤ 1 / 2 → (G.m : ℝ) ≤ (n : ℝ) ^ c → ε⁻¹ ≤ (n : ℝ) ^ c →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m) (graphInput G [] [ε]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          -- (37) with b replaced by b̄
          (H.m : ℝ) ≤ C * n * G.aggregate.dyadicClassCount * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ * Real.log n ^ 2 ∧
          (T : ℝ) ≤ C * G.m + (G.aggregate.m : ℝ) ^ (1 + g G.aggregate.m) +
            C * ((n : ℝ) ^ α * G.aggregate.dyadicClassCount * Real.log n ^ 3 +
              G.aggregate.m * Real.log n) * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹) ∧
    -- the size of the aggregated graph
    ∀ (n : ℕ) (G : Multigraph n), G.PosWeights →
      G.aggregate.m ≤ min G.m (n.choose 2) ∧
      G.aggregate.dyadicClassCount ≤ G.bClasses + ⌈Real.logb 2 G.m⌉₊ + 1 := by sorry

end DetSpectralSparsify.Dense
