-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_40
-- name    : ARTreeCover.Supplement.theorem_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:13:25.666723+00:00
-- url     : https://prove2.me/theorems/21120f85-86ee-4757-821b-9aa41289ee20
-- title:
--   Theorem 40 — almost-Ramsey embeddings into $\ell_q^{O(\log n)}$ for $(\ell,\pi)$-path-separable and $s$-vertex-separable graphs
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $\Delta>0$, $q\in[1,\infty]$, let $k>0$ be an integer, let $G$ be a connected $n$-vertex weighted graph and $L(n)=\max(1,\log_2n)$. In each case below there are $D\le C\,L(n)$ and an almost-Ramsey embedding $f:V\to\ell_q^D$ for scale $\Delta$ with distortion $Ck$ satisfying the stated number of vertices.
--
--   1. $G$ $(\ell,\pi)$-path-separable: $\dfrac{n}{C\ell L(n)^2}\,\pi^{-1/k}$ vertices.
--   2. $G$ tree-like $(\ell,\pi)$-path-separable: $\dfrac{n}{C\ell L(n)}\,\pi^{-1/k}$ vertices.
--   3. $G$ $s$-vertex-separable: $\dfrac{n}{CkL(n)}\,s^{-1/k}$ vertices.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - encoding: ℓ_q^{O(log n)}, 1 ≤ q ≤ ∞ → PiLp q (Fin D → ℝ) with D ≤ C·L(n), q : ℝ≥0∞ with 1 ≤ q; reason: the same spaces; q = ∞ is the sup norm, and the dimension bound is uniform in q
--   - encoding: "for every real parameter ϵ > 0" (resp. 0 < ϵ ≤ 1) in the hypotheses → no ϵ binder; reason: ϵ does not occur in the conclusion, so the statement for every such ϵ is equivalent to the statement without it
--   - reading: s-vertex-separable with a function s(θ) (Definition 5) → s ∈ ℕ bounds the separator of every sub-graph; reason: the theorem uses s as a number (s^{−1/k})
--   - generalization: the s-vertex-separable clause, under the opening hypothesis that G is (ℓ, π)-path-separable → s-vertex-separable alone (no path-separability assumed in that clause); reason: the Lean clause specializes to the printed one by adding the unused hypothesis; the paper derives it from Lemma 9, which uses only the vertex separators (0-length paths)
--   - encoding: (ℓ, π)-path-separable, tree-like, s-vertex-separable → IsLPiPathSeparable / IsPPathSeparable / IsVertexSeparable on every sub-graph (vertex subset, subset of the induced edges, weights inherited); reason: Definitions 5 and 6 quantify over every sub-graph
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 40, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_Supplement_HasPathSep
import Definitions.Def_ARTreeCover_Supplement_IsVertexSeparable
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyEmbedding

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 40**, p.50 (PDF p.53). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"For every real parameters ∆, ϵ > 0 and 1 ≤ q ≤ ∞, and every integer parameter k > 0, any n-vertex
connected (ℓ, π)-path-separable graph G admits an almost-Ramsey embedding f : V → ℓ_q^{O(log n)}
for scale ∆, that satisfies Ω(n/(ℓ log² n) · π^{−1/k}) vertices with stretch O(k). If G is
tree-like (ℓ, π)-path-separable, then the number of satisfied vertices is
Ω(n/(ℓ log n) · π^{−1/k}). If G is s-vertex-separable, then it admits an almost-Ramsey embedding
f : V → ℓ_q^{O(log n)} for scale ∆, that satisfies Ω(n/(k log n) · s^{−1/k}) vertices with stretch
O(k)."

**Formalization Note.**
1. `O(x)` is `C · x` and `Ω(x)` is `x / C` with one absolute `C > 0` chosen before every other
   parameter. `L(n) = max(1, log₂ n)`. "Stretch" is the distortion of Definition 23.
2. `ℓ_q^{O(log n)}` is `PiLp q (fun _ : Fin D => ℝ)` with `D ≤ C · L(n)`, for every
   `q ∈ [1, ∞]` (`q : ℝ≥0∞` with `Fact (1 ≤ q)`, `q = ∞` the sup norm); the dimension bound is part of
   the conclusion and uniform in `q`.
3. The printed `ϵ > 0` does not occur in the conclusion; the binder is dropped (equivalent).
4. The three hypotheses give three separate conclusions; the `s`-vertex-separable clause does not
   assume path-separability (a generalization). -/
theorem theorem_40 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (ℓ π s k : ℕ) (Δ : ℝ),
        0 < Δ → 0 < k → G.graph.Connected →
        (IsLPiPathSeparable G ℓ π false →
          (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
              ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * ℓ * logL (Fintype.card V) ^ 2) * (π : ℝ) ^ (-((1 : ℝ) / k))) (C * k))) ∧
        (IsLPiPathSeparable G ℓ π true →
          (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
              ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * ℓ * logL (Fintype.card V)) * (π : ℝ) ^ (-((1 : ℝ) / k))) (C * k))) ∧
        (IsVertexSeparable G s →
          (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
              ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * k * logL (Fintype.card V)) * (s : ℝ) ^ (-((1 : ℝ) / k))) (C * k))) := by sorry

end ARTreeCover.Supplement
