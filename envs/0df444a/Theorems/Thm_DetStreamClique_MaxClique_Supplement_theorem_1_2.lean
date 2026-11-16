-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_Supplement_theorem_1_2
-- name    : DetStreamClique.MaxClique.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:19:53.409198+00:00
-- url     : https://prove2.me/theorems/870282bf-42e2-4cb8-992e-8285624fe374
-- title:
--   Theorem 1.2 — deterministic one-pass maximum-independent-set space lower bound
-- statement:
--   There exist an absolute constant $c>0$ and an integer $N\ge2$ such that, for every $n\ge N$, every real $\beta$ with
--   $$1\le\beta\le\frac{\sqrt n}{36\log_2 n},$$
--   and every deterministic one-pass streaming algorithm on $\operatorname{Fin}(n)$ using $s$ bits of memory, if on every insertion-only edge stream its output is an independent set of the streamed graph $G$ of size at least $\alpha(G)/\beta$, then
--   $$s\ge c\,\frac{n^2}{\beta\log_2 n}.$$
--   The constant and threshold precede all choices of $n$, $\beta$ and the algorithm. Algorithms have unrestricted computation and edges may arrive in any order. Memory of $s$ bits means a finite state set of size at most $2^s$.
--
--   This is the paper's lower bound for Maximum Independent Set, the companion of its Maximum Clique lower bound (Theorem 1.1, the mission's goal). It shows that the folklore deterministic $O(n^2/\beta)$-bit algorithm is optimal up to a logarithmic factor for independent sets as well.
--
--   Differences from the source:
--   - encoding: an n-vertex graph and its edge-arrival streams → vertices Fin n; distinct non-loop unordered edge lists; finite states with card ≤ 2^s; reason: these represent every simple graph, every insertion order and every memory state; real division is used for approximation
--   - generalization: algorithms in the insertion-deletion streaming setting → correctness is required only on insertion-only streams; reason: every insertion-deletion algorithm restricts to such a machine with the same memory, so the Lean lower bound implies the paper's; the paper's proof (Input Distribution 4.1, §3.2 analysis) uses insertions only
--   - reading: β≤√n/36 log n → β≤√n/(36 log₂ n); reason: the same reading as the published Theorem 1.1, whose identically printed range is justified by the contribution paragraph on p. 3 (O(√n/log n)) and the rescaling in the proof on pp. 19–20; logarithms are base two (p. 6)
--   - encoding: Ω(n²/(β log n)) → ∃c>0 ∃N≥2 ∀n≥N ∀β ∀algorithm with the stated bound; reason: the asymptotic constants are uniform; N≥2 excludes undefined logarithmic denominators only below the threshold
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Theorem 1.2, p. 3 (restated §4, p. 20; proof §4, Input Distribution 4.1, pp. 20–21)

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Supplement_IndepSet

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique.Supplement

open DetStreamClique.MaxClique

/-- Theorem 1.2, p. 3 (restated p. 20); the range is read as sqrt(n)/(36 log₂ n).
Uniform constants precede n, the approximation ratio, and the algorithm. -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ β : ℝ, 1 ≤ β →
        β ≤ Real.sqrt (n : ℝ) / (36 * Real.logb 2 (n : ℝ)) →
        ∀ (S : Type) [Fintype S]
          (a : StreamingMachine (Edge n) (Finset (Fin n)) S) (s : ℕ),
          FitsBits S s → StreamCorrectIndep a β →
          c * (n : ℝ)^2 / (β * Real.logb 2 (n : ℝ)) ≤ (s : ℝ) := by sorry

end DetStreamClique.MaxClique.Supplement
