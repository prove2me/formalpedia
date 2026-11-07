-- Prove2me | Theorems.Thm_CodeSW_theorem_1
-- name    : CodeSW.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:29:36.893623+00:00
-- url     : https://prove2.me/theorems/ec3883fb-45bd-4a2f-bc78-9d16f727ff58
-- title:
--   Theorem 1 (at the strength of Corollary 17) — the Code SW chain mixes in time $2^{O(\Delta)}\cdot\mathrm{poly}(n,c,m,\beta)$
-- statement:
--   **Rapid mixing for $\Delta$-graphic or $\Delta$-cographic codes.** There are constants $C>0$ and $k\in\mathbb N$ such that the following holds for all $n,c,m,\Delta$, every parity check matrix $h\in\{0,1\}^{c\times n}$, every edge-vertex incidence matrix $g\in\{0,1\}^{c\times m}$ witnessing that $h$ is $\Delta$-graphic or $\Delta$-cographic, and every inverse temperature $\beta>0$. Let $P$ be the Code Swendsen-Wang chain for $h$ at $\beta$ and $\pi$ its Gibbs distribution. For every integer
--   $$t\ge C\,2^{C\Delta}\,(n+c+m+\beta+1)^k$$
--   one has
--   $$\max_x\|P^t(x,\cdot)-\pi\|_{\mathrm{TV}}\le\frac1{2e}.$$
--   In the notation of the paper, the chain mixes in time $2^{O(\Delta)}\cdot\mathrm{poly}(n,c,m,\beta)$ at every temperature. For $\Delta\le O(\log n)$ and $c,m=\mathrm{poly}(n)$ this is the bound $\mathrm{poly}(n,\beta)$ of Corollary 17.
--
--   This is the main rapid mixing theorem of the paper. It applies to every code whose even covers or syndrome space are, up to codimension $\Delta$, the cycle space of a graph.
--
--   Differences from the source:
--   - generalization: Definition 10 has m ≤ O(n), and Corollary 17 has ∆ ≤ O(log n), c, m = poly(n) → all n, c, m, ∆, with c, m and ∆ appearing in the bound; reason: footnote 5 notes any m = poly(n) suffices; setting c, m = poly(n), ∆ ≤ O(log n) gives Corollary 17, and with m ≤ O(n) gives Theorem 1
--   - reading: Theorem 1 writes 2^{O(∆)}·poly(n, β), with c not mentioned → c is in the polynomial; reason: Corollary 17, the formal version, assumes c = poly(n), every bound in the proof carries c, and c is not bounded by n since rows may repeat
--   - encoding: mixes in time T, with τ(P) = min_t[max_x ∑_y |P^t(x,y) − π(y)| ≤ e^{−1}] (p.13) → for all t ≥ T, distStationary P π t ≤ 1/(2e); reason: total variation is half the ℓ¹ distance and d(t) is non-increasing, so this is τ ≤ T; it avoids the junk value of an empty sInf
--   - encoding: 2^{O(∆)}·poly(n, c, m, β) → C·2^{C∆}·(n + c + m + β + 1)^k, with C and k fixed before the instance; reason: this is the meaning of the uniform asymptotic notation
--   - encoding: 'h is ∆-graphic' (there exists g) and '∆-cographic' via a column generator h^⊥ → a universally quantified witness g, with the cographic condition stated through col(h); reason: ∀g (P g → Q) is ∃g P g → Q when m may vary with g, and ker((h^⊥)ᵀ) = col(h) for every column generator
--   - reading: 'edge-vertex incidence matrix of a graph' → every row of g has exactly two ones, in distinct columns (parallel edges allowed, no loops); reason: g has one edge per check with the same row index (p.21), so repeated checks of h force parallel edges; the even-subgraph and worm arguments do not use simplicity
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Theorem 1, p.4; Corollary 17, p.19; Definition 10, p.18; mixing time, p.13

import Definitions.Def_CodeSW_cswKernel
import Definitions.Def_CodeSW_IsIncidence
import Definitions.Def_mm_mixing
open Matrix

namespace CodeSW

/-- **Theorem 1 (Rapid mixing for ∆-graphic or ∆-cographic codes), at the strength of
Corollary 17.** There are constants `C > 0` and `k ∈ ℕ` such that for every parity check matrix
`h ∈ {0,1}^{c×n}`, every edge-vertex incidence matrix `g ∈ {0,1}^{c×m}` witnessing that `h` is
∆-graphic or ∆-cographic, and every inverse temperature `β > 0`, the Code SW chain is within
total variation `1/(2e)` of the Gibbs distribution from every start after any
`t ≥ C·2^{C∆}·(n + c + m + β + 1)^k` steps; i.e. it mixes in time `2^{O(∆)}·poly(n, c, m, β)`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Theorem 1, p.4; Corollary 17, p.19).

**Formalization Note** The mixing time `τ(P) = min_t [max_x ∑_y |P^t(x,y) − π(y)| ≤ e^{−1}]` of
p.13 is an `ℓ¹` threshold, i.e. total variation `≤ 1/(2e)`; "`τ ≤ T`" is stated as the bound for
every `t ≥ T` (equivalent, since `d(t)` is non-increasing). `C` and `k` are fixed before
`n, c, m, ∆, h, g, β`. `m ≤ O(n)` (Definition 10) and `∆ ≤ O(log n)`, `c, m = poly(n)`
(Corollary 17) are not imposed; `c` and `m` appear in the polynomial. -/
theorem theorem_1 :
    ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
      ∀ (n c m Δ : ℕ) (h : Matrix (Fin c) (Fin n) (ZMod 2))
        (g : Matrix (Fin c) (Fin m) (ZMod 2)) (β : ℝ), 0 < β →
        (IsDeltaGraphicVia h g Δ ∨ IsDeltaCographicVia h g Δ) →
        ∀ t : ℕ, C * (2 : ℝ) ^ (C * (Δ : ℝ)) * ((n : ℝ) + c + m + β + 1) ^ k ≤ (t : ℝ) →
          MarkovMixing.distStationary (cswKernel h β) (gibbs h β) t ≤ 1 / (2 * Real.exp 1) := by sorry

end CodeSW
