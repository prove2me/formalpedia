-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_theorem_1_1
-- name    : DetStreamClique.MaxClique.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:08:01.531004+00:00
-- url     : https://prove2.me/theorems/b86c3f80-d037-4770-9230-9b7507b5c9f4
-- title:
--   Theorem 1.1 — deterministic one-pass maximum-clique space lower bound
-- statement:
--   There exist an absolute constant $c>0$ and an integer $N\ge2$ such that, for every $n\ge N$, every real $\beta$ with
--   $$1\le\beta\le\frac{\sqrt n}{36\log_2 n},$$
--   and every deterministic one-pass streaming algorithm on $\operatorname{Fin}(n)$ using $s$ bits, if its output is a clique of size at least $\omega(G)/\beta$ on every insertion-only stream, then
--   $$s\ge c\,\frac{n^2}{\beta\log_2 n}.$$
--   The constant and threshold precede all choices of $n$, $\beta$ and the algorithm. Algorithms have unrestricted computation and may process edges in any order. This is the paper's full maximum-clique lower bound, with a constant uniform in the approximation ratio.
--
--   Differences from the source:
--   - encoding: an n-vertex graph and its edge-arrival streams → vertices Fin n; distinct non-loop unordered edge lists; finite states with card ≤ 2^s; reason: these represent every simple graph, every insertion order and every memory state; real division is used for approximation
--   - generalization: algorithms in the insertion-deletion streaming setting → correctness is required only on insertion-only streams; reason: every insertion-deletion algorithm restricts to such a machine with the same memory; the paper proof uses insertions only
--   - reading: β≤√n/36 log n → β≤√n/(36 log₂ n); reason: the contribution paragraph on p. 3 gives O(√n/log n), and the proof on pp. 19–20 uses gadget parameter b=β log₂ n with b≤√n/36
--   - encoding: Ω(n²/(β log n)) → ∃c>0 ∃N≥2 ∀n≥N ∀β ∀algorithm with the stated bound; reason: the asymptotic constants are uniform; N≥2 excludes undefined logarithmic denominators only below the threshold
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Theorem 1.1; proof §3.2.6, p. 3; pp. 19–20

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Graphs

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Theorem 1.1, p. 3; the range is read as sqrt(n)/(36 log₂ n).
Uniform constants precede n, the approximation ratio, and the algorithm. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ β : ℝ, 1 ≤ β →
        β ≤ Real.sqrt (n : ℝ) / (36 * Real.logb 2 (n : ℝ)) →
        ∀ (S : Type) [Fintype S]
          (a : StreamingMachine (Edge n) (Finset (Fin n)) S) (s : ℕ),
          FitsBits S s → StreamCorrect a β →
          c * (n : ℝ)^2 / (β * Real.logb 2 (n : ℝ)) ≤ (s : ℝ) := by sorry

end DetStreamClique.MaxClique
