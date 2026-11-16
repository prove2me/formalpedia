-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_Supplement_theorem_17
-- name    : DetSpectralSparsify.Dense.Supplement.theorem_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:31.497301+00:00
-- url     : https://prove2.me/theorems/c79ef8e1-c9da-4ce2-a57d-cc0a1bea0f71
-- title:
--   Theorem 17 (The r-level algorithm) — $A_r$ is a $(1\pm\eta)^{r+1}$ approximation with (41) edges in (42) time, uniformly in $r$
-- statement:
--   There are implementation data of Algorithms 4–6 meeting their specification, a sequence $\phi_n\in(0,1]$ with $\phi_n^{-1}=\log^{9+h(n)}n$ and $h(n)\to0$, and a function $g(m)\to0$, with the following property. Let $\alpha_0>2$ be a rational achievable matrix multiplication exponent and let $\alpha_r$ be given by (40). There is one program such that for every $c$ there is a constant $C>0$, the same for all levels $r$, with: for every positively weighted multigraph $G$ with $n\ge2$ vertices and $m\le n^c$ edges whose non-loop edge weights occupy at most $b$ dyadic classes $[2^a,2^{a+1})$, every $0<\eta\le1/2$ and every $r\ge0$,
--
--   1. every graph $H$ returned by a run of $A_r(G,\eta)$ (Algorithm 9) satisfies
--   $$(1-\eta)^{r+1}L_G\;\preceq\;L_H\;\preceq\;(1+\eta)^{r+1}L_G$$
--   and has
--   $$|E(H)|\;\le\;C\,n\,\bigl(b+(r+1)\ln n\bigr)\,\phi_n^{-2}\eta^{-2}\ln^2 n\tag{41}$$
--   edges;
--   2. the program, given $G$, $r$ and $\eta$, halts with the output of a run of $A_r(G,\eta)$ after at most
--   $$(r+1)\,m^{1+g(m)}\;+\;C\,n^{\alpha_r}\bigl(b+(r+1)\ln n\bigr)\,\phi_n^{-5}\eta^{-9/2}\ln^5 n\tag{42}$$
--   steps.
--
--   With $\eta=\varepsilon/(4(r+1))$ and $r=\lceil\ln n\rceil$ this gives the deterministic sparsifier of Theorem 19; Theorem 17 is the result that ties the exponent recurrence (40) to the running time.
--
--   **Formalization Note** The machine is the mission's closed real RAM; the input is `graphInput G [r] [η]` (natural parameter $r$, real parameter $\eta$), the output is read by `decodeGraph`, and the word bound uses the base $2+n+m+r$. $b$ bounds the number `dyadicClassCount` of occupied classes of the non-loop edges, not the spread $1+\lceil\log_2(w_{\max}/w_{\min})\rceil$. The program and $g$ are fixed before $c$, and $C$ before $r$, $n$, $G$, $b$ and $\eta$; there is no restriction on $\eta^{-1}$ relative to $n$, because $A_r$ returns $\bar G$ when $n<\eta^{-1}$.
--
--   Differences from the source:
--   - generalization: A_r with the fixed choices of Algorithms 4–8 → every run of the execution relation for the chosen implementation data (any removal order, Euler tour, greedy order, expander decomposition meeting Theorem 13's guarantees, scores within the Lemma 6 tolerance), with the spectral bound and (41) asserted for every run; reason: every fixed implementation is one run, and the program's own output is required to be a run
--   - reading: α₀ = ω and the cost n^ω → every rational achievable exponent α₀ > 2 (one program multiplies n × n matrices in O(n^{α₀}) steps); reason: the program computes s = ⌈n^{1/(α_{r−1}−1)}⌉ from α₀, which a fixed program can do exactly for rational α₀ (the paper itself evaluates the recurrence at the rational ω̃ = 2.371339, Figure 1), while ω need not be attained; this is the mission's achievable-exponent reading of n^ω
--   - reading: the paper names no machine model → the mission's closed real RAM, input graphInput G [r] [η], output decodeGraph, word bound base 2 + n + m + r; reason: r is part of the input, so the word bound must admit it
--   - reading: Theorem 13 applied to F[U] gives conductance ϕ_n → the decomposition of Algorithm 7 meets ϕ_n with n the number of vertices of Algorithm 7's input; reason: Algorithm 7 line 11 uses that same ϕ_n for every cluster
--   - reading: Algorithm 9 line 7 partitions V(G) into V_1, …, V_t, each of size at most s → consecutive blocks, vertex v in block ⌊v/s⌋, so ⌈n/s⌉ blocks of size s except possibly the last; reason: the source fixes no particular partition, and its proof counts O(n²/s²) block pairs, which requires ⌈n/s⌉ blocks of size about s; consecutive blocks are the natural deterministic choice
--   - generalization: standing convention that isolated vertices are discarded (p.5) → isolated vertices allowed, counted in n; reason: Algorithm 9 is defined on such graphs and the bounds only grow with n
--   - encoding: m^{1+o(1)}, O(·), log → m^{1+g(m)} with g → 0 fixed before the input, one constant C for each polynomial regime m ≤ n^c chosen before r, natural logarithm; reason: the uniform-in-r reading required by the use of Theorem 17 with r = ⌈ln n⌉ in Theorem 19
--   - encoding: all n → n ≥ 2; reason: for n ≤ 1 the factor ln n vanishes and the time bound would force a run of at most (r+1)·m^{1+g(m)} steps on edgeless inputs; the source's bounds with log n concern n ≥ 2
--   - encoding: operators on U = (D^{1/2}𝟏)^⊥ → zero-extended matrices on ℝ^N, P as the functional calculus of x ↦ x^{-1/2} with value 0 at 0; reason: the traces in Algorithm 1 are unchanged
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.29, Theorem 17 ((41), (42); proof pp.29–30); Algorithm 9 p.29, recurrence (40) p.28

import Definitions.Def_DetSpectralSparsify_Dense_Supplement_RLevel

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense.Supplement

open DetSpectralSparsify.Dense

/-- Theorem 17 (The r-level algorithm), p.29 (proof pp.29–30). There are implementation data of
Algorithms 4–6 meeting their specification, a conductance sequence `ϕ_n = log^{-9-h(n)} n` with
`h → 0` and `g → 0` such that, for every rational achievable matrix-multiplication exponent
`α₀ > 2` (the paper's `α₀ = ω`), there is one program and, for every `c`, one `C` working for all
levels `r` simultaneously: for every positively weighted `n`-vertex (`n ≥ 2`), `m`-edge multigraph
`G` whose non-loop weights occupy at most `b` dyadic classes, every `0 < η ≤ 1/2`, every `r ≥ 0`
and `m ≤ n^c`,
* every output `H` of `A_r(G, η)` (Algorithm 9) satisfies
  `(1 − η)^{r+1} L_G ⪯ L_H ⪯ (1 + η)^{r+1} L_G` and has at most
  `C n (b + (r+1) log n) ϕ_n⁻² η⁻² log² n` edges (41);
* the program, given `G`, `r` and `η`, halts with an output of `A_r(G, η)` after at most
  `(r+1) m^{1+g(m)} + C n^{α_r} (b + (r+1) log n) ϕ_n⁻⁵ η^{-9/2} log⁵ n` steps (42),
  `α_r` from (40). -/
theorem theorem_17 :
    ∃ (D : ImplData) (ϕ h g : ℕ → ℝ), D.Spec ∧ IsPhiSequence ϕ h ∧ Vanishing g ∧
    ∀ α₀ : ℚ, 2 < α₀ → Achievable (α₀ : ℝ) →
    ∃ (P : Program) (K : ℕ), ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (r n : ℕ) (G : Multigraph n) (η : ℝ) (b : ℕ),
      2 ≤ n → G.PosWeights → G.dyadicClassCount ≤ b → 0 < η → η ≤ 1 / 2 →
      (G.m : ℝ) ≤ (n : ℝ) ^ c →
      (∀ H : Multigraph n, RLevel D ϕ α₀ r G η H →
        PSDLe ((1 - η) ^ (r + 1) • G.laplacian) H.laplacian ∧
        PSDLe H.laplacian ((1 + η) ^ (r + 1) • G.laplacian) ∧
        -- (41)
        (H.m : ℝ) ≤ C * n * (b + (r + 1) * Real.log n) * (ϕ n)⁻¹ ^ 2 * (η ^ 2)⁻¹ *
          Real.log n ^ 2) ∧
      ∃ (T : ℕ) (s' : State) (H : Multigraph n),
        RunsWithin P K (2 + n + G.m + r) (graphInput G [r] [η]) T s' ∧
        decodeGraph n s' = some H ∧ RLevel D ϕ α₀ r G η H ∧
        -- (42)
        (T : ℝ) ≤ (r + 1) * (G.m : ℝ) ^ (1 + g G.m) +
          C * (n : ℝ) ^ alphaSeq (α₀ : ℝ) r * (b + (r + 1) * Real.log n) * (ϕ n)⁻¹ ^ 5 *
            η ^ (-(9 / 2 : ℝ)) * Real.log n ^ 5 := by sorry

end DetSpectralSparsify.Dense.Supplement
