-- Prove2me | Theorems.Thm_FengLiYangMatching_General_online_feasibility
-- name    : FengLiYangMatching.General.online_feasibility
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T16:53:08.382197+00:00
-- url     : https://prove2.me/theorems/555c7732-029a-41fb-bea2-d3246016918d
-- title:
--   Algorithm 1 — matching feasibility and irrevocability
-- statement:
--   Let $a\le b$ be real phase boundaries. For every finite chronological stream of loopless unordered edges, Algorithm 1 returns a matching consisting of edges in that stream. For every stream, including streams with repeated edges, the actual matching can only grow as the processed prefix grows:
--
--   $$
--   M_j\subseteq M_k\qquad(j\le k).
--   $$
--
--   The chronological matching assertion and this persistence property establish feasibility at every prefix of a valid execution. The transition sees only the arriving observation and its current state.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018, Algorithm 1, p. 3; the formal statement extends feasibility to repeated edges and persistence to arbitrary streams; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General
theorem online_feasibility (a b : ℝ) (hab : a ≤ b) :
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      (l.map (fun o => o.2.1)).Pairwise (· ≤ ·) →
      (∀ o ∈ l, ¬ o.1.IsDiag) →
        IsMatching (run a b l).actual ∧
        (run a b l).actual ⊆ (l.map (fun o => o.1)).toFinset) ∧
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      ∀ j k : ℕ, j ≤ k →
        (run a b (l.take j)).actual ⊆ (run a b (l.take k)).actual) := by sorry
end FengLiYangMatching.General
