-- Prove2me | Theorems.Thm_DetConnSketch_Main_lemma_4_5
-- name    : DetConnSketch.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:23.443201+00:00
-- url     : https://prove2.me/theorems/5df2deed-64cc-4e9a-ab3f-c1dd45b627c4
-- title:
--   Lemma 4.5 — a sign matrix $X\in\{\pm1\}^{n\times\tilde O(t)}$ whose rows on any $|U|\le t$ are independent and separate $U$ from its complement
-- statement:
--   There is a universal constant $C > 0$ such that for all $n$ and $t$ there is a matrix $X \in \{\pm1\}^{n\times D}$ with $D \le C(t+1)\log^C(n+2)$ such that for every $U \subseteq [n]$ with $|U| \le t$:
--   1. the rows of $X$ indexed by $U$ are linearly independent (over $\mathbb R$);
--   2. there is $h \in \mathbb R^D$ with
--   $$(Xh)_v = 0 \ \ (v \in U), \qquad (Xh)_v > 0 \ \ (v \notin U).$$
--   One matrix $X$ serves all such $U$ simultaneously.
--
--   In Lemma 4.2 the vector $h$ isolates the edges leaving a small vertex cover, and the independence of the rows on $U$ kills the rest.
--
--   Differences from the source:
--   - reading: X ∈ {±1}^{n×Õ(t)} → ∃ C > 0 (before n and t): D ≤ C (t + 1) (log (n+2))^C; reason: explicit Õ with one universal constant; t + 1 because U = ∅ already needs D ≥ 1 when n ≥ 1, and n + 2 avoids log 1 = 0
--   - encoding: vertex set [n] = {1, …, n} → Fin n (0-based); reason: Lean indexing; same objects
--   - encoding: rows X|_U linearly independent; vector h → LinearIndependent ℝ of the real rows indexed by U; h : Fin D → ℝ and (Xh)_v = ∑_j X v j · h j; reason: same statement over ℝ
--   - encoding: parameter t in the cardinality condition |U| ≤ t → t : ℕ; reason: for any real t ≥ 0, use ⌊t⌋; the eligible subsets are unchanged and the dimension upper bound only increases
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 23 (PDF 27), Lemma 4.5; p. 31 (PDF 35)

import Mathlib

namespace DetConnSketch.Main

/-- Lemma 4.5 (`Õ(t)` columns, one universal constant `C`): for every `n` and `t` there is a
sign matrix `X ∈ {±1}^{n×D}` with `D ≤ C (t + 1) (log (n+2))^C` such that for every
`U ⊆ [n]` with `|U| ≤ t`: (1) the rows of `X` indexed by `U` are linearly independent over `ℝ`;
(2) some `h ∈ ℝ^D` has `(Xh)_v = 0` for `v ∈ U` and `(Xh)_v > 0` for `v ∉ U`. -/
theorem lemma_4_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n t : ℕ, ∃ (D : ℕ) (X : Matrix (Fin n) (Fin D) ℤ),
      (D : ℝ) ≤ C * ((t : ℝ) + 1) * Real.log ((n : ℝ) + 2) ^ C ∧
      (∀ i j, X i j = 1 ∨ X i j = -1) ∧
      ∀ U : Finset (Fin n), U.card ≤ t →
        LinearIndependent ℝ (fun u : U => fun j : Fin D => (X u j : ℝ)) ∧
        ∃ h : Fin D → ℝ, ∀ v : Fin n,
          (v ∈ U → ∑ j, (X v j : ℝ) * h j = 0) ∧
          (v ∉ U → 0 < ∑ j, (X v j : ℝ) * h j) := by sorry

end DetConnSketch.Main
