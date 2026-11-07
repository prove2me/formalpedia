-- Prove2me | Theorems.Thm_DynEdgeOrient_lemma_3_1
-- name    : DynEdgeOrient.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:46.802429+00:00
-- url     : https://prove2.me/theorems/5d89d58d-e61f-4c6a-99bf-9f703351b770
-- title:
--   Lemma 3.1 (batch out-degree reduction): $O(\Phi\log((\delta-2\alpha)|V|/\Phi))$ flips reach the targets $c$
-- statement:
--   Let $H$ be a loop-free multigraph on the finite vertex set $V$ with arboricity at most $\alpha$, oriented so that every out-degree is at most $\delta$, where $\delta>2\alpha$. Let $c:V\to\{2\alpha,\dots,\delta\}$ be target out-degrees, let $e(v)=\max\{0,d^+(v)-c(v)\}$ be the excess of $v$, and let $\Phi=\sum_{v\in V}e(v)$. There is an absolute constant $C$ such that some orientation $\sigma'$ satisfies $d^+_{\sigma'}(v)\le c(v)$ for every $v$ and differs from the given orientation on at most
--
--   $$
--   C\,\Phi\,\log_2\frac{(\delta-2\alpha)|V|}{\Phi}
--   $$
--
--   edges.
--
--   The lemma reduces a total excess $\Phi$ at a cost only logarithmic in the ratio of the slack $(\delta-2\alpha)|V|$ to $\Phi$. Lemma 5.2 applies it inside each node of the hierarchy.
--
--   **Formalization Note** A sequence of flips is represented by its end orientation; the edges on which the two orientations differ can be flipped one at a time. At $\Phi=0$ the bound is $0$.
--
--   Differences from the source:
--   - encoding: a graph (multigraph with parallel edges, no loops) → an edge-label type E with endpoint map ends and the hypothesis (ends e).1 ≠ (ends e).2; states are finite label sets; reason: parallel edges are distinct labels with equal endpoints; every loop-free multigraph is such an instance
--   - encoding: a sequence of O(Φ log((δ−2α)|V|/Φ)) flips reaching out-degrees ≤ c → an orientation σ' with out-degrees ≤ c that differs from σ on at most C·Φ·log₂((δ−2α)|V|/Φ) edges, C absolute and chosen first; reason: flipping the differing edges one by one is such a sequence, and every such sequence flips at least those edges; the base of the logarithm changes only C
--   - encoding: e(v) = max{0, d⁺(v) − c(v)} → d⁺(v) − c(v) in ℕ; reason: truncated subtraction is max{0, ·}
--   - encoding: arboricity ≤ α, i.e. max_{|U| ≥ 2} ⌈|E(U)|/(|U|−1)⌉ ≤ α → |E(S)| ≤ α(|S| − 1) for every vertex set S, in ℕ; reason: equivalent; for |S| ≤ 1 both sides are 0 since there are no loops
--   - reading: δ > 2α and c : V → [2α, δ] (interval not stated as integer) → δ : ℕ and c : V → ℕ with 2α ≤ c(v) ≤ δ; reason: out-degrees are integers, so d⁺(v) ≤ c(v) iff d⁺(v) ≤ ⌊c(v)⌋ and a real δ reduces to ⌊δ⌋ (the bound only grows with δ; if ⌊δ⌋ = 2α then Φ = 0); with a fractional c the printed bound would be false (one overfull vertex with excess ε needs a flip while ε·log(K/ε) → 0), so the integer interval is the only true reading
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Lemma 3.1, p.10 (pdf p.11)

import Mathlib
import Definitions.Def_DynEdgeOrient_Orientation

namespace DynEdgeOrient

/-- **Lemma 3.1 (Batch out-degree reduction)** (Hiken–Wein, STOC 2027 submission, manuscript
sha256 626b4eee…, Lemma 3.1, p.10). Let `H = (V, E)` be a `δ`-oriented digraph with arboricity
`≤ α`, for some `δ > 2α`. Let `c : V → [2α, δ]` be target out-degrees, `e(v) = max{0, d⁺(v) − c(v)}`
the excess and `Φ = Σ_v e(v)`. There is a sequence of `O(Φ · log((δ − 2α)|V| / Φ))` flips after
which every `v` has out-degree `≤ c(v)`.

**Formalization Note.**
* The constant `C` is absolute and chosen first.
* A sequence of flips is represented by its end result `σ'`: flipping the edges on which `σ` and
  `σ'` differ, one at a time, is such a sequence, and any sequence reaching `σ'` flips at least
  those edges. The count is `#{e ∈ F : σ e ≠ σ' e}`.
* `Φ = Σ_v (d⁺(v) − c(v))` in `ℕ`; truncated subtraction is exactly `max{0, ·}`.
* Logarithm base 2 (another base changes only `C`). At `Φ = 0` the bound is `0` (Lean's
  `0 · log(x/0) = 0`), and no flip is needed. -/
theorem lemma_3_1 :
    ∃ C : ℝ, ∀ (V E : Type*) [Fintype V] [DecidableEq V] [DecidableEq E]
      (ends : E → V × V) (_ : ∀ e, (ends e).1 ≠ (ends e).2) (F : Finset E) (α δ : ℕ)
      (σ : E → Bool) (c : V → ℕ),
      ArboricityLE ends F α → 2 * α < δ → (∀ v, outDeg ends F σ v ≤ δ) →
      (∀ v, 2 * α ≤ c v ∧ c v ≤ δ) →
      ∃ σ' : E → Bool, (∀ v, outDeg ends F σ' v ≤ c v) ∧
        ((F.filter (fun e => σ e ≠ σ' e)).card : ℝ) ≤
          C * (∑ v, (outDeg ends F σ v - c v) : ℕ) *
            Real.logb 2 (((δ : ℝ) - 2 * α) * Fintype.card V /
              (∑ v, (outDeg ends F σ v - c v) : ℕ)) := by sorry

end DynEdgeOrient
