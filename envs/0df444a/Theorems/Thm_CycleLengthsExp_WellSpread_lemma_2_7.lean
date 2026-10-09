-- Prove2me | Theorems.Thm_CycleLengthsExp_WellSpread_lemma_2_7
-- name    : CycleLengthsExp.WellSpread.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:56.484971+00:00
-- url     : https://prove2.me/theorems/74c1411a-9d1b-4abe-9fb9-9405cd8e7c0d
-- title:
--   Lemma 2.7, p. 7 — a rooted tree with levels k₀ ≤ k₁ ≤ k₂, bounded degree on T[k₁,k₂], and an (n/10, α/5)-expander inside T[k₁,k₂]
-- statement:
--   For every $0<\alpha\le1$ there are positive constants $\Delta=O(1/\alpha^5)$, $C_0=O(1/\alpha)$, $C_1=O(1/\alpha^5)$ and $C_2=O(1/\alpha)$ with the following property. For every $\alpha$-expander $G$ on $n$ vertices and every vertex $v_0$, $G$ contains a tree $T$ rooted at $v_0$, with levels $L_1=\{v_0\},\dots,L_{k_0},\dots,L_{k_1},\dots,L_{k_2}$ ($1\le k_0\le k_1\le k_2$, the last level $L_{k_2}$ non-empty), such that
--
--   1. $k_0\le C_0\log_2 n$, $\;k_1-k_0\le C_1$, $\;k_2-k_1\le C_2$;
--   2. $k_0$ is the first index with $|T_{[1,k_0]}|\ge\alpha^4n/200$;
--   3. every $v\in T_{[k_1,k_2]}$ has degree at most $\Delta$ in $T$;
--   4. $T_{[k_1,k_2]}$ contains a vertex set $U$ with $|U|\ge n/10$ such that $G[U]$ is an $(n/10,\alpha/5)$-expander.
--
--   This is the main lemma of the paper: a tree of logarithmic depth whose middle band has bounded degree and carries an expander. Theorem 1 routes all of its cycles through such a tree.
--
--   **Formalization Note.** The $O(\cdot)$ bounds use one absolute constant $K>0$, fixed before $\alpha$: $\Delta,C_1\le K/\alpha^5$ and $C_0,C_2\le K/\alpha$. The statement is asserted for all $n\ge n_0(\alpha)$, a threshold depending on $\alpha$ only: the page has no threshold but its proof suppresses rounding and needs $n$ large against $1/\alpha$; Theorem 1 applies the lemma only for large $n$. $T$ is a subgraph of $G$ that is a tree; levels are $1+$ the distance from $v_0$ in $T$; every vertex of $T$ lies on a level $\le k_2$. Item 2 reads: $|T_{[1,k_0]}|\ge\alpha^4n/200$ and $|T_{[1,j]}|<\alpha^4n/200$ for $1\le j<k_0$. The expander of item 4 uses the edges of $G$ (induced subgraph).
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 7, Lemma 2.7

import Mathlib
import Definitions.Def_CycleLengthsExp_WellSpread_Setting

namespace CycleLengthsExp.WellSpread

theorem lemma_2_7 :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∃ Δ C₀ C₁ C₂ : ℝ, 0 < Δ ∧ Δ ≤ K / α ^ 5 ∧ 0 < C₀ ∧ C₀ ≤ K / α ∧
        0 < C₁ ∧ C₁ ≤ K / α ^ 5 ∧ 0 < C₂ ∧ C₂ ≤ K / α ∧
        ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ G : SimpleGraph (Fin n), IsAlphaExpander α G →
          ∀ v₀ : Fin n, ∃ T : G.Subgraph, v₀ ∈ T.verts ∧ T.coe.IsTree ∧
            ∃ k₀ k₁ k₂ : ℕ, 1 ≤ k₀ ∧ k₀ ≤ k₁ ∧ k₁ ≤ k₂ ∧
              T.verts = levelSet T v₀ 1 k₂ ∧ (levelSet T v₀ k₂ k₂).Nonempty ∧
              -- item 1
              (k₀ : ℝ) ≤ C₀ * Real.logb 2 n ∧ ((k₁ : ℝ) - k₀) ≤ C₁ ∧ ((k₂ : ℝ) - k₁) ≤ C₂ ∧
              -- item 2
              α ^ 4 * n / 200 ≤ ((levelSet T v₀ 1 k₀).ncard : ℝ) ∧
              (∀ j : ℕ, 1 ≤ j → j < k₀ → ((levelSet T v₀ 1 j).ncard : ℝ) < α ^ 4 * n / 200) ∧
              -- item 3
              (∀ v ∈ levelSet T v₀ k₁ k₂, ((T.neighborSet v).ncard : ℝ) ≤ Δ) ∧
              -- item 4
              ∃ U : Set (Fin n), U ⊆ levelSet T v₀ k₁ k₂ ∧ (n : ℝ) / 10 ≤ (U.ncard : ℝ) ∧
                IsKAlphaExpander ((n : ℝ) / 10) (α / 5) (G.induce U) := by sorry

end CycleLengthsExp.WellSpread
