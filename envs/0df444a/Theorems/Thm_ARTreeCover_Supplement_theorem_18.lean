-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_18
-- name    : ARTreeCover.Supplement.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:06:41.612919+00:00
-- url     : https://prove2.me/theorems/bf184e18-c992-4e10-ac40-bae6087733d1
-- title:
--   Theorem 18 — layered pairwise and neighborhood covers of $(\ell,\pi)$-path-separable and $s$-vertex-separable graphs (corrected: $\min(\epsilon,1)$ in $\sigma$)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph, $\epsilon,\Delta>0$ real, $k>0$ an integer, $\epsilon_1=\min(\epsilon,1)$ and $L(n)=\max(1,\log_2n)$.
--
--   1. If $G$ is $(\ell,\pi)$-path-separable, it admits a strong $\sigma$-layered $(\Delta,(2k-1)(1+\epsilon))$-pairwise cover and a strong $\sigma$-layered $(\Delta,(4k-2)(1+\epsilon))$-neighborhood cover, both with $\sigma\le C\,\ell\,(\pi/\epsilon_1)^{1/k}L(n)^2$.
--   2. If $G$ is tree-like $(\ell,\pi)$-path-separable, the same holds with $\sigma\le C\,\ell\,k\,(\pi/\epsilon_1)^{1/k}L(n)$.
--   3. If $G$ is $s$-vertex-separable, it admits a strong $\sigma$-layered $(\Delta,2k-1)$-pairwise cover and a strong $\sigma$-layered $(\Delta,4k-2)$-neighborhood cover, both with
--   $$\sigma\le C\,k\,s^{1/k}L(n).$$
--
--   With Lemma 14 these covers give Theorem 21, and with Lemma 16 they give Theorem 26.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - correction: σ = O(ℓ·(π/ϵ)^{1/k}·log² n) and O(ℓ·k·(π/ϵ)^{1/k}·log n) for every ϵ > 0 → ϵ replaced by min(ϵ, 1) inside σ only; the radius blow-ups keep ϵ; reason: as printed, for any constant C the one-vertex graph, which is (1, 1)-path-separable, gets σ < 1 layers once ϵ > C^k, but needs one layer; for ϵ ≤ 1 the statement is the printed one, and for ϵ > 1 it follows from the case ϵ = 1 because a larger radius blow-up is weaker
--   - reading: s-vertex-separable with a function s(θ) (Definition 5) → s ∈ ℕ bounds the separator of every sub-graph; reason: the theorem uses s as a number (s^{1/k}; "contains at most s vertices", p.25)
--   - generalization: the s-vertex-separable clause, under the opening hypothesis that G is (ℓ, π)-path-separable → s-vertex-separable alone (no path-separability assumed in that clause); reason: the Lean clause specializes to the printed one by adding the unused hypothesis; the paper derives it from Lemma 9, which uses only the vertex separators (0-length paths)
--   - encoding: (ℓ, π)-path-separable, tree-like, s-vertex-separable → IsLPiPathSeparable / IsPPathSeparable / IsVertexSeparable on every sub-graph (vertex subset, subset of the induced edges, weights inherited); reason: Definitions 5 and 6 quantify over every sub-graph
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 18, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_IsPairwiseCover
import Definitions.Def_ARTreeCover_Supplement_HasPathSep
import Definitions.Def_ARTreeCover_Supplement_IsVertexSeparable

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 18**, p.27 (PDF p.30). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex undirected weighted (ℓ, π)-path-separable graph, let ϵ, ∆ > 0 be real
parameters, and let k > 0 be an integer parameter. Then, G admits a strong σ-layered
(∆, (2k − 1)(1 + ϵ))-pairwise cover and a strong σ-layered (∆, (4k − 2)(1 + ϵ))-neighborhood cover,
both with σ = O(ℓ · (π/ϵ)^{1/k} · log² n). If G is tree-like (ℓ, π)-path-separable, then in both
results, σ = O(ℓ · k · (π/ϵ)^{1/k} · log n). If G is s-vertex-separable, then it admits a strong
σ-layered (∆, 2k − 1)-pairwise cover and a strong σ-layered (∆, 4k − 2)-neighborhood cover, both
with σ = O(k · s^{1/k} · log n)."

**Formalization Note.**
1. One absolute `C > 0`, chosen before every other parameter, serves every O(·).
   `L(n) = max(1, log₂ n)`.
2. Correction: inside σ, `ϵ` is replaced by `min(ϵ, 1)` (radius blow-ups keep `ϵ`). As printed for
   every `ϵ > 0` the bound falls below one layer when `ϵ → ∞`, which is false for a one-vertex
   graph; for `ϵ ≤ 1` the statement is the printed one.
3. The three hypotheses give three separate conclusions (a conjunction of implications); the
   tree-like and `s`-vertex-separable clauses are additional results, not alternatives.
   `s`-vertex-separable uses `s : ℕ` as a number (`IsVertexSeparable`). The `s`-vertex-separable
   clause does not assume path-separability (a generalization of the printed context; the paper
   derives it from Lemma 9, which uses only vertex separators). -/
theorem theorem_18 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (ℓ π s k : ℕ) (ε Δ : ℝ),
        0 < ε → 0 < Δ → 0 < k →
        (IsLPiPathSeparable G ℓ π false →
          (∃ m : ℕ, (m : ℝ) ≤ C * ℓ * ((π : ℝ) / min ε 1) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ Pi : Fin m → Finpartition (Finset.univ : Finset V),
              IsPairwiseCover G true Δ ((2 * (k : ℝ) - 1) * (1 + ε)) Pi) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ℓ * ((π : ℝ) / min ε 1) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ Pi : Fin m → Finpartition (Finset.univ : Finset V),
              IsNeighborhoodCover G true Δ ((4 * (k : ℝ) - 2) * (1 + ε)) Pi)) ∧
        (IsLPiPathSeparable G ℓ π true →
          (∃ m : ℕ, (m : ℝ) ≤ C * ℓ * k * ((π : ℝ) / min ε 1) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ∧ ∃ Pi : Fin m → Finpartition (Finset.univ : Finset V),
              IsPairwiseCover G true Δ ((2 * (k : ℝ) - 1) * (1 + ε)) Pi) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ℓ * k * ((π : ℝ) / min ε 1) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ∧ ∃ Pi : Fin m → Finpartition (Finset.univ : Finset V),
              IsNeighborhoodCover G true Δ ((4 * (k : ℝ) - 2) * (1 + ε)) Pi)) ∧
        (IsVertexSeparable G s →
          (∃ m : ℕ, (m : ℝ) ≤ C * k * (s : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ∧ ∃ Pi : Fin m → Finpartition (Finset.univ : Finset V),
              IsPairwiseCover G true Δ (2 * (k : ℝ) - 1) Pi) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * k * (s : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ∧ ∃ Pi : Fin m → Finpartition (Finset.univ : Finset V),
              IsNeighborhoodCover G true Δ (4 * (k : ℝ) - 2) Pi)) := by sorry

end ARTreeCover.Supplement
