-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_theorem_14
-- name    : DetSpectralSparsify.Dense.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:14.289476+00:00
-- url     : https://prove2.me/theorems/83b4eb42-f9eb-43e6-83cb-eb50453d1654
-- title:
--   Theorem 14 (Deterministic sparsification at one weight scale) — (34), (35), (36) and the log^{…+o(1)}(n/ε) forms
-- statement:
--   There are a sequence $\phi_n=\log^{-9-o(1)}n$, functions $g,h_1,\dots,h_4\to0$, a sparse program, and for every achievable exponent $\alpha>2$ a dense program, such that for every $c$ there is $C$ with the following property. Let $G$ be an $n$-vertex, $m$-edge weighted multigraph ($n\ge2$, no isolated vertex) whose non-loop edge weights lie in $[1,2]$, let $0<\varepsilon\le1/2$, and suppose $m,\varepsilon^{-1}\le n^c$. Both programs construct a $(1\pm\varepsilon)$-spectral sparsifier $H$ of $G$ (a reweighted subgraph) with
--   $$|E(H)|\le C\,n\,\phi_n^{-2}\varepsilon^{-2}\log^2n,\qquad |E(H)|\le C\,n\,\varepsilon^{-2}\log^{20+h_1(n)}(n/\varepsilon) \tag{34}$$
--   edges. The dense implementation runs in
--   $$m^{1+g(m)}+C(n^{\alpha}\log^3n+m\log n)\,\phi_n^{-2}\varepsilon^{-2}
--   \;\text{ and }\; m^{1+g(m)}+C\big(n^{\alpha}\varepsilon^{-2}\log^{21+h_2(n)}(n/\varepsilon)+m\varepsilon^{-2}\log^{19+h_3(n)}(n/\varepsilon)\big)\tag{35}$$
--   steps, and the sparse implementation in
--   $$m^{1+g(m)}+C\,nm\,\phi_n^{-3}\varepsilon^{-5/2}\log^3n
--   \;\text{ and }\; m^{1+g(m)}+C\,nm\,\varepsilon^{-5/2}\log^{30+h_4(n)}(n/\varepsilon)\tag{36}$$
--   steps.
--
--   Applied to every dyadic weight class, this gives the weighted algorithm (Theorem 15).
--
--   **Formalization Note** Input $(G,\varepsilon)$ in `graphInput G [] [ε]`, output by `decodeGraph`. The sequence $\phi$ and the functions $g,h_i$ are fixed before $c$; $C$ depends only on $c$ (and on $\alpha$ for the dense program).
--
--   Differences from the source:
--   - reading: a deterministic algorithm running in the stated time (the paper fixes no machine model) → a fixed program of the closed real RAM `Program` (natural +, truncated −; real + − × ÷ √, ℕ→ℝ cast, comparisons; no floor, real constants or oracles) halting within the stated number of steps, with natural words of O(log(input + T)) bits, input and output in the layouts `graphInput`/`decodeGraph`; reason: the paper names no model; arithmetic complexity on real weights is the natural reading, and the closed instruction set prevents a step from hiding unbounded work
--   - reading: dense time with the factor n^ω, ω the infimum of matrix multiplication exponents (p.5) → for every α > 2 with `Achievable α` (some program multiplies n×n real matrices in C(n+1)^α steps) there is a dense program whose bound has n^α; reason: ω need not be attained; the bound is meaningful for exponents actually achieved by an algorithm, and holds for every one of them; α > 2 is the explicit reading prescribed by the BRIEF, allowing lower-degree polylogarithmic work to be absorbed in n^α
--   - encoding: ϕ_n := log^{−9−o(1)} n → a sequence ϕ : ℕ → (0,1] and h → 0 with ϕ(n)⁻¹ = (log n)^{9+h(n)} for n ≥ 3 (`IsPhiSequence`), chosen before the instances; reason: spells out the o(1); ϕ cannot be an arbitrarily small free parameter
--   - encoding: O(·), m^{1+o(1)} and m, ε⁻¹ ≤ n^{O(1)} → the program and the functions g → 0 (steps ≤ m^{1+g(m)} + …) are fixed first; then for every c ∈ ℕ there is C > 0 such that every instance with m ≤ n^c and ε⁻¹ ≤ n^c meets the bounds with constant C; each log^{k+o(1)}(n/ε) is (log(n/ε))^{k+h_i(n)} with h_i → 0 fixed first; reason: standard quantifier order for these asymptotic claims: constants are uniform over graphs, weights and accuracies
--   - generalization: standing assumption ε⁻¹ ≤ n in every theorem that produces a spectral sparsifier (p.5), plus ε⁻¹ ≤ n^{O(1)} → only ε⁻¹ ≤ n^c is assumed; reason: covers every source instance; for ε⁻¹ > n the source itself notes that the whole graph after aggregating parallel edges (at most n² edges) suffices, which fits the stated bounds
--   - generalization: weighted multigraph (positive weights) with non-loop weights in [1,2] → self-loops of any nonnegative weight; reason: loops do not enter L_G; positive loop weights are a special case
--   - reading: a (1 ± ε)-spectral sparsifier: a weighted graph H on V(G) with (1−ε)L_G ⪯ L_H ⪯ (1+ε)L_G (Definition 2) → H additionally is a reweighted subgraph of G: each edge of H has positive weight and joins two distinct vertices joined by a non-loop edge of G (`IsReweightedSubgraph`); reason: the abstract and p.1 describe the output as a reweighted subgraph; the stronger reading is the one the algorithm delivers (every recursive output is supported on its input)
--   - encoding: n-vertex graph (bounds contain log n) → hypothesis 2 ≤ n; reason: at n = 1 we have log n = 0 and the O-bounds degenerate to 0; a one-vertex graph has zero Laplacian and nothing to sparsify
--   - encoding: standing convention 'we discard isolated vertices' (§2, p.5) → hypothesis `G.NoIsolated` (every vertex is an endpoint of some edge); reason: the section's standing assumption made explicit as a binder; it excludes no instance the source considers
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.23, Theorem 14 (with Algorithm 7)

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Theorem 14 (Deterministic sparsification at one weight scale), p.23. For an `n`-vertex,
`m`-edge multigraph with non-loop weights in `[1, 2]`, `0 < ε ≤ 1/2` and `m, ε⁻¹ ≤ n^{O(1)}`, a
deterministic program constructs a `(1 ± ε)`-spectral sparsifier with `O(n ϕ_n⁻² ε⁻² log² n)` edges
(34); its sparse implementation runs in `m^{1+o(1)} + O(n m ϕ_n⁻³ ε^{-5/2} log³ n)` time (36) and,
for every achievable exponent `α > 2`, its dense implementation in
`m^{1+o(1)} + O((n^α log³ n + m log n) ϕ_n⁻² ε⁻²)` time (35); with `ϕ_n⁻¹ = log^{9+o(1)} n` these
are `O(n ε⁻² log^{20+o(1)}(n/ε))` edges and the stated `log^{…+o(1)}(n/ε)` times. -/
theorem theorem_14 :
    ∃ (ϕ h g h₁ h₂ h₃ h₄ : ℕ → ℝ), IsPhiSequence ϕ h ∧ Vanishing g ∧ Vanishing h₁ ∧
      Vanishing h₂ ∧ Vanishing h₃ ∧ Vanishing h₄ ∧
    (∃ (P : Program) (K : ℕ), ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (ε : ℝ),
        2 ≤ n → G.NoIsolated → G.NonloopWeightsIn 1 2 → G.LoopsNonneg →
        0 < ε → ε ≤ 1 / 2 → (G.m : ℝ) ≤ (n : ℝ) ^ c → ε⁻¹ ≤ (n : ℝ) ^ c →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m) (graphInput G [] [ε]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          -- (34) and its restatement
          (H.m : ℝ) ≤ C * n * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ * Real.log n ^ 2 ∧
          (H.m : ℝ) ≤ C * n * (ε ^ 2)⁻¹ * Real.log (n / ε) ^ (20 + h₁ n) ∧
          -- (36) and its restatement
          (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
            C * n * G.m * (ϕ n)⁻¹ ^ 3 * ε ^ (-(5 / 2 : ℝ)) * Real.log n ^ 3 ∧
          (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
            C * n * G.m * ε ^ (-(5 / 2 : ℝ)) * Real.log (n / ε) ^ (30 + h₄ n)) ∧
    ∀ α : ℝ, 2 < α → Achievable α →
    ∃ (P : Program) (K : ℕ), ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : Multigraph n) (ε : ℝ),
        2 ≤ n → G.NoIsolated → G.NonloopWeightsIn 1 2 → G.LoopsNonneg →
        0 < ε → ε ≤ 1 / 2 → (G.m : ℝ) ≤ (n : ℝ) ^ c → ε⁻¹ ≤ (n : ℝ) ^ c →
        ∃ (T : ℕ) (s' : State) (H : Multigraph n),
          RunsWithin P K (2 + n + G.m) (graphInput G [] [ε]) T s' ∧
          decodeGraph n s' = some H ∧ IsSparsifierOutput ε G H ∧
          -- (34) and its restatement
          (H.m : ℝ) ≤ C * n * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ * Real.log n ^ 2 ∧
          (H.m : ℝ) ≤ C * n * (ε ^ 2)⁻¹ * Real.log (n / ε) ^ (20 + h₁ n) ∧
          -- (35) and its restatement
          (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
            C * ((n : ℝ) ^ α * Real.log n ^ 3 + G.m * Real.log n) * (ϕ n)⁻¹ ^ 2 * (ε ^ 2)⁻¹ ∧
          (T : ℝ) ≤ (G.m : ℝ) ^ (1 + g G.m) +
            C * ((n : ℝ) ^ α * (ε ^ 2)⁻¹ * Real.log (n / ε) ^ (21 + h₂ n) +
              G.m * (ε ^ 2)⁻¹ * Real.log (n / ε) ^ (19 + h₃ n)) := by sorry

end DetSpectralSparsify.Dense
