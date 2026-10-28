-- Prove2me | Theorems.Thm_DirectedOpinion_Typical_theorem_1
-- name    : DirectedOpinion.Typical.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:42.475848+00:00
-- url     : https://prove2.me/theorems/6425fe89-16c3-4c0c-8c8a-4efa0127f328
-- title:
--   Theorem 1, p. 5 — on a locally finite directed graph with d > 0, R^(k) ⇒ R = Σ_r Δ^r W^(r) at the geometric rate (1 − d)^k (2/d + 2)
-- statement:
--   Let $G$ be a fixed locally finite vertex-weighted directed graph on a countable vertex set $V$, with weights in $[0,1]$ summing to $c$ at every vertex with $d_i^->0$, where $c\in[0,1)$, $d\in(0,1]$, $c+d\le1$. Let the signals $W_i^{(k)}$, $k\ge0$, $i\in V$, be independent random variables, identically distributed in $k$ for each $i$, with $|W_i^{(k)}|\le d+c-\sum_rc(i,r)$. Let $R=\sum_{r\ge0}\Delta^rW^{(r)}$ be the stationary vector. Then:
--   1. $R\in[-1,1]^V$;
--   2. for every initial vector $R^{(0)}\in[-1,1]^V$, the opinion process of recursion (1) satisfies
--   $$R^{(k)}\Rightarrow R,\qquad k\to\infty ,$$
--   weakly on $\mathbb R^V$ with the product topology;
--   3. the convergence is geometric: for every finite set $F\subseteq V$, every $k$ and every $f:\mathbb R^F\to\mathbb R$ that is 1-Lipschitz for the sup distance,
--   $$\bigl|E f(R^{(k)}|_F)-E f(R|_F)\bigr|\le(1-d)^k\Bigl(\frac2d+2\Bigr).$$
--
--   The limit $R$ is a function of the signals alone, so it does not depend on the law of $R^{(0)}$. On a random graph the theorem is applied to each realization of the graph.
--
--   **Formalization Note**
--   1. The vertex set is countable, so that the Borel and product σ-algebras of $\mathbb R^V$ agree; every locally finite graph used in the paper is countable.
--   2. On a fixed graph the attributes are constants, so "conditionally i.i.d. given $\mathbf x_i$" becomes i.i.d. in time.
--   3. The limit is the explicit vector of the proof ($R=\tilde B-\mathbf 1$, p. 23), which is stronger than its existence.
--   4. "Geometric rate" is given the meaning of item 3, with the constant of the proof (p. 23: $\|\tilde R^{(k)}-\tilde B\|_\infty\le(1-d)^k(2/d+2)$).
--   5. No independence between $R^{(0)}$ and the signals is assumed; none is needed.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 5, Theorem 1; rate from the proof of Theorem 1, pp. 22–23

import Mathlib
import Definitions.Def_DirectedOpinion_Typical_Model

namespace DirectedOpinion.Typical

open MeasureTheory ProbabilityTheory Set Filter

/-- Theorem 1, p. 5 (with the rate of its proof, p. 23). On a fixed locally finite directed graph
with countably many vertices, with `d > 0` and signals that are independent over vertices and
times, identically distributed in time at each vertex and bounded by the budget, the stationary
vector `R = Σ_r Δ^r W^(r)` (a function of the signals only) takes values in `[−1, 1]^V`, and for
every measurable initial vector `R^(0)` with values in `[−1, 1]`:
(b) `R^(k) ⇒ R` as `k → ∞` (weak convergence on `ℝ^V` with the product topology);
(c) for every finite set `F` of vertices, every `k` and every `f` that is 1-Lipschitz for the sup
distance on `ℝ^F`, `|E f(R^(k)|_F) − E f(R|_F)| ≤ (1 − d)^k (2/d + 2)`. -/
theorem theorem_1 {V Ω : Type*} [Countable V] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : WDigraph V) (c d : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1) (hG : G.Valid c) (hlf : G.LocallyFinite)
    (W : ℕ → V → Ω → ℝ) (hWm : ∀ k i, Measurable (W k i))
    (hWind : iIndepFun (fun p : ℕ × V => W p.1 p.2) P)
    (hWid : ∀ k i, IdentDistrib (W k i) (W 0 i) P P)
    (hWb : ∀ k i ω, |W k i ω| ≤ G.budget c d i) :
    (∀ ω i, stationary G c d (fun k j => W k j ω) i ∈ Icc (-1 : ℝ) 1) ∧
    ∀ R0 : Ω → V → ℝ, Measurable R0 → (∀ ω i, R0 ω i ∈ Icc (-1 : ℝ) 1) →
      TendstoInDistribution (fun k ω => opinion G c d (R0 ω) (fun t j => W t j ω) k) atTop
          (fun ω => stationary G c d (fun t j => W t j ω)) (fun _ => P) P ∧
        ∀ (F : Finset V) (f : (F → ℝ) → ℝ), LipschitzWith 1 f → ∀ k : ℕ,
          |(∫ ω, f (fun j => opinion G c d (R0 ω) (fun t i => W t i ω) k j) ∂P) -
              ∫ ω, f (fun j => stationary G c d (fun t i => W t i ω) j) ∂P| ≤
            (1 - d) ^ k * (2 / d + 2) := by sorry

end DirectedOpinion.Typical
