-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_21
-- name    : ARTreeCover.Supplement.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:07:23.236971+00:00
-- url     : https://prove2.me/theorems/84f6c257-6347-4fc4-a77a-96a50a77711f
-- title:
--   Theorem 21 — minor-closed $(\ell,\pi)$-path-separable graphs have spanning forest and HST covers with stretch $(4k-2)(1+\epsilon)$, almost-Ramsey with $(8k-4)(1+\epsilon)$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted graph such that $G$ and every minor of $G$ are $(\ell,\pi)$-path-separable, let $0<\epsilon\le1$, let $k>0$ be an integer and $L(n)=\max(1,\log_2n)$. With
--   $$M=C\,\epsilon^{-1}\,\ell\,(\pi/\epsilon)^{1/k}\,L(n)^3,$$
--   the graph $G$ admits
--
--   1. a spanning forest cover and an HST cover, both of size at most $M$ and stretch at most $(4k-2)(1+\epsilon)$;
--   2. a spanning almost-Ramsey forest cover and an almost-Ramsey HST cover, both of size at most $M$ and stretch $(8k-4)(1+\epsilon)$.
--
--   If $G$ and every minor of $G$ are tree-like $(\ell,\pi)$-path-separable, the same four covers exist with size at most $C\,\epsilon^{-1}\,\ell\,k\,(\pi/\epsilon)^{1/k}L(n)^2$.
--
--   This applies to $K_r$-minor-free and bounded-genus graphs (Corollary 5).
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - reading: "If G is tree-like (ℓ, π)-path-separable, then the size of all these covers is …" → G and every minor of G are tree-like (ℓ, π)-path-separable; reason: the sentence substitutes "tree-like (ℓ, π)-path-separable" into the theorem's hypothesis, which is about G and its minors; the proof (p.34) applies the tree-like bound of Theorem 18 to every minor G*, as Lemma 14 requires
--   - encoding: every minor of G → every weighted minor H of G (WMinor) on any finite vertex type; reason: a minor of a finite graph is finite; quantifying over all types builds in "up to isomorphism"
--   - encoding: almost-Ramsey forest/HST cover with stretch α → the cover predicate, the stretch predicate and the almost-Ramsey predicate with the same α; reason: almost-Ramsey with stretch α implies stretch α (take ∆ = d_G(u, v)); the published theorem_19 uses the same encoding
--   - encoding: (ℓ, π)-path-separable → IsLPiPathSeparable / IsPPathSeparable / IsVertexSeparable on every sub-graph (vertex subset, subset of the induced edges, weights inherited); reason: Definitions 5 and 6 quantify over every sub-graph
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 21, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WMinor
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover
import Definitions.Def_ARTreeCover_Supplement_HasPathSep

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 21**, p.34 (PDF p.37). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G = (V, E) be an n-vertex (ℓ, π)-path-separable graph, such that every minor of G is
(ℓ, π)-path-separable as well. Let 0 < ϵ ≤ 1 be a real parameter, and let k > 0 be an integer
parameter. Then, G admits a spanning forest cover an HST cover, both with size
O(1/ϵ · ℓ · (π/ϵ)^{1/k} · log³ n) and stretch (4k − 2)(1 + ϵ). Moreover, G admits a spanning
almost-Ramsey forest cover and an almost-Ramsey HST cover with the same size and stretch
(8k − 4)(1 + ϵ). If G is tree-like (ℓ, π)-path-separable, then the size of all these covers is
O(1/ϵ · ℓ · k · (π/ϵ)^{1/k} · log² n)."

**Formalization Note.**
1. One absolute `C > 0`, chosen before every other parameter, serves every O(·).
   `L(n) = max(1, log₂ n)`.
2. Minors are the published weighted minors `WMinor` on any finite vertex type.
3. Reading of the last sentence: "tree-like" replaces "(ℓ, π)-path-separable" in the whole
   hypothesis, i.e. `G` and every minor of `G` are tree-like `(ℓ, π)`-path-separable (the proof on
   p.34 applies the tree-like bound of Theorem 18 to every minor).
4. Almost-Ramsey covers are also stated with stretch, which almost-Ramsey implies (as in the
   published `theorem_19`). -/
theorem theorem_21 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (ℓ π k : ℕ) (ε : ℝ),
        0 < ε → ε ≤ 1 → 0 < k →
        IsLPiPathSeparable G ℓ π false →
        (∀ (W : Type) [Fintype W] [DecidableEq W] (H : WGraph W), WMinor H G →
          IsLPiPathSeparable H ℓ π false) →
        ((∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 3 ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).IsSpanning G) ∧
            IsForestCover G T ∧
            ForestStretchLE G T ((4 * (k : ℝ) - 2) * (1 + ε))) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 3 ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H ((4 * (k : ℝ) - 2) * (1 + ε))) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 3 ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).IsSpanning G) ∧
            IsForestCover G T ∧
            ForestStretchLE G T ((8 * (k : ℝ) - 4) * (1 + ε)) ∧
            ForestAlmostRamsey G T ((8 * (k : ℝ) - 4) * (1 + ε))) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 3 ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H ((8 * (k : ℝ) - 4) * (1 + ε)) ∧
            HSTAlmostRamsey G H ((8 * (k : ℝ) - 4) * (1 + ε)))) ∧
        ((IsLPiPathSeparable G ℓ π true ∧
            ∀ (W : Type) [Fintype W] [DecidableEq W] (H : WGraph W), WMinor H G →
              IsLPiPathSeparable H ℓ π true) →
          (∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * k * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).IsSpanning G) ∧
            IsForestCover G T ∧
            ForestStretchLE G T ((4 * (k : ℝ) - 2) * (1 + ε))) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * k * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H ((4 * (k : ℝ) - 2) * (1 + ε))) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * k * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).IsSpanning G) ∧
            IsForestCover G T ∧
            ForestStretchLE G T ((8 * (k : ℝ) - 4) * (1 + ε)) ∧
            ForestAlmostRamsey G T ((8 * (k : ℝ) - 4) * (1 + ε))) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * ε⁻¹ * ℓ * k * ((π : ℝ) / ε) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H ((8 * (k : ℝ) - 4) * (1 + ε)) ∧
            HSTAlmostRamsey G H ((8 * (k : ℝ) - 4) * (1 + ε)))) := by sorry

end ARTreeCover.Supplement
