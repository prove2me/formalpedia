-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_26
-- name    : ARTreeCover.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:10:38.781387+00:00
-- url     : https://prove2.me/theorems/e0ecda4e-0bc1-430b-a310-8db12223afdb
-- title:
--   Theorem 26 — spanning almost-Ramsey trees and HSTs for $(\ell,\pi)$-path-separable and $s$-vertex-separable graphs (corrected: $\min(\epsilon,1)$ in the counts)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $\Delta,\epsilon>0$, let $k>0$ be an integer, let $G$ be a connected $n$-vertex weighted graph, $\epsilon_1=\min(\epsilon,1)$ and $L(n)=\max(1,\log_2n)$. In each case below $G$ has a spanning almost-Ramsey tree $T$ and an almost-Ramsey HST $H$ for scale $\Delta$, each satisfying the stated number of vertices with the stated stretch.
--
--   1. $G$ $(\ell,\pi)$-path-separable: $\dfrac{n}{C\ell L(n)^2}\left(\dfrac{\pi}{\epsilon_1}\right)^{-1/k}$ vertices, stretch $(8k-4)(1+\epsilon)$.
--   2. $G$ tree-like $(\ell,\pi)$-path-separable: $\dfrac{n}{C\ell L(n)}\left(\dfrac{\pi}{\epsilon_1}\right)^{-1/k}$ vertices, stretch $(8k-4)(1+\epsilon)$.
--   3. $G$ $s$-vertex-separable: $\dfrac{n}{CkL(n)}\,s^{-1/k}$ vertices, stretch $8k-4$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - correction: Ω(n/(ℓ log² n)·(π/ϵ)^{−1/k}) and Ω(n/(ℓ log n)·(π/ϵ)^{−1/k}) for every ϵ > 0 → ϵ replaced by min(ϵ, 1) in the counts; the stretch keeps ϵ; reason: as printed, the count grows like ϵ^{1/k} without bound, so the two-vertex graph with one edge ((1, 1)-path-separable) would need more than 2 satisfied vertices for large ϵ; for ϵ ≤ 1 the statement is the printed one, and for ϵ > 1 it follows from ϵ = 1 because a larger stretch is weaker
--   - reading: s-vertex-separable with a function s(θ) (Definition 5) → s ∈ ℕ bounds the separator of every sub-graph; reason: the theorem uses s as a number (s^{−1/k})
--   - generalization: the s-vertex-separable clause, under the opening hypothesis that G is (ℓ, π)-path-separable → s-vertex-separable alone (no path-separability assumed in that clause); reason: the Lean clause specializes to the printed one by adding the unused hypothesis; the paper derives it from Lemma 9, which uses only the vertex separators (0-length paths)
--   - encoding: (ℓ, π)-path-separable, tree-like, s-vertex-separable → IsLPiPathSeparable / IsPPathSeparable / IsVertexSeparable on every sub-graph (vertex subset, subset of the induced edges, weights inherited); reason: Definitions 5 and 6 quantify over every sub-graph
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 26, p.38 (PDF p.41)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_Supplement_HasPathSep
import Definitions.Def_ARTreeCover_Supplement_IsVertexSeparable
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyTree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 26**, p.38 (PDF p.41). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"For every real parameters ∆, ϵ > 0 and every integer parameter k > 0, any n-vertex connected
(ℓ, π)-path-separable graph G admits a spanning almost-Ramsey tree T and an almost-Ramsey HST H for
scale ∆, that satisfies Ω(n/(ℓ log² n) · (π/ϵ)^{−1/k}) vertices with stretch (8k − 4)(1 + ϵ). If G
is tree-like (ℓ, π)-path-separable, then the number of satisfied vertices is
Ω(n/(ℓ log n) · (π/ϵ)^{−1/k}). If G is s-vertex-separable, then it admits a spanning almost-Ramsey
tree T and an almost-Ramsey HST H for scale ∆, that satisfies Ω(n/(k log n) · s^{−1/k}) vertices
with stretch 8k − 4."

**Formalization Note.**
1. `Ω(x)` is `x / C` with one absolute `C > 0` chosen before every other parameter.
   `L(n) = max(1, log₂ n)`; negative powers are `Real.rpow`.
2. Correction: in the counts, `ϵ` is replaced by `min(ϵ, 1)` (the stretch keeps `ϵ`). As printed for
   every `ϵ > 0` the count `(π/ϵ)^{−1/k}` grows without bound as `ϵ → ∞`; for `ϵ ≤ 1` it is the
   printed statement.
3. The three hypotheses give three separate conclusions (a conjunction of implications); the
   `s`-vertex-separable clause does not assume path-separability (a generalization). -/
theorem theorem_26 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (ℓ π s k : ℕ) (Δ ε : ℝ),
        0 < Δ → 0 < ε → 0 < k → G.graph.Connected →
        (IsLPiPathSeparable G ℓ π false →
          (∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * ℓ * logL (Fintype.card V) ^ 2) * ((π : ℝ) / min ε 1) ^ (-((1 : ℝ) / k))) ((8 * (k : ℝ) - 4) * (1 + ε))) ∧
            (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * ℓ * logL (Fintype.card V) ^ 2) * ((π : ℝ) / min ε 1) ^ (-((1 : ℝ) / k))) ((8 * (k : ℝ) - 4) * (1 + ε)))) ∧
        (IsLPiPathSeparable G ℓ π true →
          (∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * ℓ * logL (Fintype.card V)) * ((π : ℝ) / min ε 1) ^ (-((1 : ℝ) / k))) ((8 * (k : ℝ) - 4) * (1 + ε))) ∧
            (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * ℓ * logL (Fintype.card V)) * ((π : ℝ) / min ε 1) ^ (-((1 : ℝ) / k))) ((8 * (k : ℝ) - 4) * (1 + ε)))) ∧
        (IsVertexSeparable G s →
          (∃ T : WForest V, T.IsSpanning G ∧ IsAlmostRamseyTree G T Δ ((Fintype.card V : ℝ) / (C * k * logL (Fintype.card V)) * (s : ℝ) ^ (-((1 : ℝ) / k))) (8 * (k : ℝ) - 4)) ∧
            (∃ H : HST V, IsAlmostRamseyHST G H Δ ((Fintype.card V : ℝ) / (C * k * logL (Fintype.card V)) * (s : ℝ) ^ (-((1 : ℝ) / k))) (8 * (k : ℝ) - 4))) := by sorry

end ARTreeCover.Supplement
