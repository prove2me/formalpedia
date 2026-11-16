-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_Supplement_theorem_A_1
-- name    : DetStreamClique.MaxClique.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:20:32.352589+00:00
-- url     : https://prove2.me/theorems/dc1b87a0-df7a-49e1-9677-e4329f01b2bd
-- title:
--   Theorem A.1 — deterministic insertion-deletion O(n²/β)-bit algorithms for approximate clique and independent set
-- statement:
--   There exist an absolute constant $C>0$ and an integer $N$ such that, for every $n\ge N$ and every real $\beta$ with
--   $$1\le\beta\le\frac{n}{\log_2 n},$$
--   the following two statements hold.
--
--   1. There is a deterministic one-pass insertion-deletion streaming algorithm on $\operatorname{Fin}(n)$ that, on every legal insertion-deletion edge stream, outputs a clique of the final graph $G$ of size at least $\omega(G)/\beta$, using $s$ bits of memory with
--   $$s\le C\,\frac{n^2}{\beta}.$$
--   2. There is a deterministic one-pass insertion-deletion streaming algorithm on $\operatorname{Fin}(n)$ that, on every legal insertion-deletion edge stream, outputs an independent set of the final graph $G$ of size at least $\alpha(G)/\beta$, using $s\le C\,n^2/\beta$ bits of memory.
--
--   The constant $C$ and the threshold $N$ are the same for both problems and precede $n$, $\beta$ and the algorithm; the algorithm may depend on $n$ and $\beta$. Algorithms have unrestricted computation; memory of $s$ bits means a finite state set of size at most $2^s$. A legal stream starts from the empty graph, inserts only absent edges and deletes only present ones, and may have any length.
--
--   This is the folklore derandomisation of the randomised algorithm of Halldórsson, Sun, Szegedy and Wang, recorded in the paper for completeness. Together with Theorems 1.1 and 1.2 it shows that the deterministic space complexity of both problems is $n^2/\beta$ up to a logarithmic factor in the range $\beta=O(\sqrt n/\log n)$.
--
--   Differences from the source:
--   - encoding: insertion-deletion edge streams on an n-vertex graph → lists of ins/del updates of non-loop unordered pairs of Fin n, legal when every insertion adds an absent edge and every deletion removes a present one, with correctness evaluated on the final graph of surviving edges; reason: this is the paper's model on p. 2 (output valid for the final set of surviving edges); stream length and re-insertions are unrestricted
--   - encoding: space of a deterministic one-pass algorithm → a finite state type of card ≤ 2^s; reason: memory states are exactly what s bits can encode; computation is unrestricted as on p. 2
--   - reading: "computes either a β-approximate Maximum Clique or Maximum Independent Set" → both: one algorithm for each problem, under the same constant; reason: the proof on p. 25 treats both problems by the same construction, and the disjunctive reading would be weaker
--   - encoding: O(n²/β) for β ≤ n/log n → ∃C>0 ∃N ∀n≥N ∀β∈[1, n/log₂ n] with s ≤ C·n²/β; reason: the constant is uniform in n, β and the problem; β ≥ 1 is the paper's standing range (p. 2) and logarithms are base two (p. 6)
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Appendix A, Theorem A.1 and its proof, p. 25

import Mathlib
import Definitions.Def_DetStreamClique_MaxClique_Supplement_InsDel

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique.Supplement

open DetStreamClique.MaxClique SpanForestStream.Unrestricted

/-- Theorem A.1, p. 25: for 1 ≤ β ≤ n / log₂ n there is a deterministic one-pass
insertion-deletion streaming algorithm for β-approximate Maximum Clique, and one for
β-approximate Maximum Independent Set, each using at most C·n²/β bits; the constant C
and threshold N precede n, β and the problem. -/
theorem theorem_A_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ β : ℝ, 1 ≤ β →
        β ≤ (n : ℝ) / Real.logb 2 (n : ℝ) →
        (∃ (S : Type) (_ : Fintype S)
            (a : StreamingMachine (Update n) (Finset (Fin n)) S) (s : ℕ),
            FitsBits S s ∧ (s : ℝ) ≤ C * (n : ℝ)^2 / β ∧ InsDelCorrectClique a β) ∧
        (∃ (S : Type) (_ : Fintype S)
            (a : StreamingMachine (Update n) (Finset (Fin n)) S) (s : ℕ),
            FitsBits S s ∧ (s : ℝ) ≤ C * (n : ℝ)^2 / β ∧ InsDelCorrectIndep a β) := by sorry

end DetStreamClique.MaxClique.Supplement
