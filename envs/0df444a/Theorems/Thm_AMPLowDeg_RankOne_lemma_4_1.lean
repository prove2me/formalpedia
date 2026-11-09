-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_4_1
-- name    : AMPLowDeg.RankOne.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:06:36.64181+00:00
-- url     : https://prove2.me/theorems/37793230-4084-4d91-b1b4-b49066294017
-- title:
--   Lemma 4.1 — leaf removal (4.4)
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$, $s>0$, $\eta=\eta_s$, and let $C_\alpha$ be the graph cumulants (4.3). Suppose $v\ne1$ is a vertex of degree one in $\alpha$ and $(v,w)\in\alpha$, and write $\alpha-v$ for the multi-index obtained by deleting the unique edge incident to $v$. Then for every $h\in\mathbb R^n$ the map $h_w\mapsto C_{\alpha-v}(h)$ is differentiable and
--
--   $$
--   C_\alpha(h)=\eta(h_v)\,\partial_{h_w}C_{\alpha-v}(h).
--   $$
--
--   Iterating the identity peels off trees attached to a graph; it gives the product formula for tree cumulants in Lemma 2.4 and the reduction to cores in Lemma 6.1.
--
--   Differences from the source:
--
--   - generalization: s = q_AMP > 0, fixed throughout the graph argument (p. 11) → every s > 0; reason: the statement holds for every s > 0 and specializes to s = q_AMP, which is positive by Lemma A.7
--   - encoding: ∂_{h_w} C_{α−v}(h) → ∃ d with HasDerivAt (t ↦ C_{α−v}(h with h_w := t)) d (h_w) and C_α(h) = η(h_v)·d; reason: states the differentiability that the partial derivative presupposes instead of using a junk deriv
--   - encoding: (v, w) ∈ α and α − v → 0 < α(mkEdge v w), and α − v decrements that multiplicity by one; reason: a degree-one vertex lies on exactly one edge copy, so the decrement deletes it
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 11, Lemma 4.1, eq. (4.4); proof pp. 11–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential
import Definitions.Def_AMPLowDeg_RankOne_Graph
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- Lemma 4.1, p. 11 — leaf removal (4.4): if `v ≠ 1` has degree one in `α` and `(v, w) ∈ α`, and
`α − v` deletes that edge, then `h_w ↦ C_{α−v}(h)` is differentiable and
`C_α(h) = η(h_v) ∂_{h_w} C_{α−v}(h)` for every `h ∈ ℝⁿ`. Vertex `1` is `⟨0, hn⟩`. -/
theorem lemma_4_1 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s)
    (α : Edge n → ℕ) (v w : Fin n) (hv : v ≠ ⟨0, hn⟩) (hdeg : deg α v = 1)
    (hvw : 0 < α (mkEdge v w)) (h : Fin n → ℝ) :
    ∃ d : ℝ, HasDerivAt (fun t : ℝ => Ccum π s ⟨0, hn⟩
        (Function.update α (mkEdge v w) (α (mkEdge v w) - 1)) (Function.update h w t)) d (h w) ∧
      Ccum π s ⟨0, hn⟩ α h = eta π s (h v) * d := by sorry

end AMPLowDeg.RankOne
