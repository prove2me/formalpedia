-- Prove2me | Theorems.Thm_DynOracleConn_Supplement_theorem_7_9
-- name    : DynOracleConn.Supplement.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:51:06.303472+00:00
-- url     : https://prove2.me/theorems/3aa225d6-f7eb-4eae-9b80-c03c24a18997
-- title:
--   Theorem 7.9 = Theorem 1(c), p.49 — space $\tilde O(S)$ and total time $\tilde O(k(1+\min\{n,k\}/S))$ (list), $\tilde O(nk(1+\min\{n,k\}/S))$ (matrix) over the first $k$ updates
-- statement:
--   For every constant $c>0$ there are constants $C>0$, $e\in\mathbb N$ and $a\ge1$, a list-model program $P_{\mathrm{list}}$ and a matrix-model program $P_{\mathrm{mat}}$ of the word RAM with the following property. Let $n\ge2$ and $1\le S\le n$ be integers, run the programs with words of $a\lceil\log_2(n+1)\rceil$ bits, and write $L=\log_2n$. For all terminals $s,t$ and every insertion-only sequence $\sigma$, the following hold.
--
--   1. **List model**, for every sequence of adjacency-list orderings. On every outcome of the random words, the space used is at most $C\,S\,L^e$ words. With probability at least $1-n^{-c}$, every update completes with the correct answer, and for every $1\le k\le|\sigma|$ both the total time and the total number of queries of the first $k$ updates are at most
--   $$C\,k\Big(1+\frac{\min\{n,k\}}{S}\Big)L^e.$$
--   2. **Matrix model.** On every outcome, the space is at most $C\,S\,L^e$ words. With probability at least $1-n^{-c}$, every update completes with the correct answer, and for every $1\le k\le|\sigma|$ the total time of the first $k$ updates is at most
--   $$C\,n\,k\Big(1+\frac{\min\{n,k\}}{S}\Big)L^e.$$
--
--   This is the random-walk landmark algorithm, the paper's main algorithmic result. Over $m$ insertions its total time is $\tilde O(mn/S)$ in the list model. By Theorem 4, no fully dynamic algorithm can beat these amortized bounds in either model.
--
--   **Formalization Note** The matrix clause is the matrix-model bound of Theorem 1(c). The paper derives it by simulating each list query with a row scan of the adjacency matrix, using $O(n)$ queries and $O(1)$ words. A step is one executed instruction, oracle calls included.
--
--   Differences from the source:
--   - generalization: "Let n ≥ 2 and 1 ≤ S ≤ n … There is a randomized algorithm" → one program chosen before n and S (after c), which receives n, s, t, S as input words; reason: p.4: "At initialization, the algorithm is given n, s, t, and S"; a single program gives one for each n, S; a program chosen after n could keep the whole graph in its program counter, which is not charged as memory
--   - reading: Õ(·): factors polynomial in log n suppressed (footnote 1, p.1) → ∃ C > 0, k ∈ ℕ chosen after c and before n, S, s, t, i and σ, with the bound multiplied by (log₂ n)^k; reason: the definition of Õ with constants independent of the instance
--   - encoding: the word RAM: words of Θ(log n) bits, time = word operations including oracle calls, space = words of all writable memory → the machine of Supplement.Machine with words of a⌈log₂(n + 1)⌉ bits (a fixed with C, k); time = executed instructions; space = 1 + the largest address accessed, cumulative; reason: the paper names the model and no instruction set; a standard unit-cost instruction set
--   - encoding: with probability at least 1 − n^{−c} → the measure of the failure set is at most n^{−c}; reason: for a non-measurable failure set this bounds its outer measure, so the success event contains a measurable set of probability ≥ 1 − n^{−c}
--   - encoding: "for every update sequence"; guarantees against output-adaptive adversaries → every incremental (valid, insertion-only) sequence and terminals s, t fixed in advance; reason: §7, p.42: the adaptive case reduces to sequences and orderings fixed in advance
--   - encoding: [n]; vertex labels; Neighbor(v, j) outside [d(v)] → vertices coded 0, …, n − 1; Neighbor returns the code w + 1, or 0 outside [d(v)]; reason: Lean conventions; same instances
--   - reading: the list model: neighbors "in an arbitrary ordering" → every sequence of orderings ρ k, one per update, fixed in advance; reason: §7, p.42: "the update sequence and adjacency-list orderings have been fixed in advance"; the guarantees hold for every ordering
--   - reading: "a randomized algorithm with space Õ(S) … such that … with probability at least 1 − n^{−c}" → the space bound on every random tape (for an update that never completes: the supremum over its run); reason: the space clause stands outside the probability clause (p.4 says bounds hold w.h.p. "unless stated otherwise"); the stronger reading is chosen, and it is true because the algorithm can cap its landmark set and fail inside the n^{−c} event
--   - reading: Theorem 7.9 (list model) and "the matrix-model bound of Theorem 1(c)" → both clauses in one item: list (total time and queries) and matrix (total time Õ(nk(1 + min{n, k}/S)), space Õ(S)); reason: Theorem 1(c) states the matrix bound and the sentence after Theorem 7.9 derives it; the matrix clause bounds time only, as printed
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 7.9, p.49 and the sentence after it; Theorem 1(c), p.5

import Mathlib
import Definitions.Def_DynOracleConn_Supplement_Exec

namespace DynOracleConn

namespace Supplement

/-- **Theorem 7.9 = Theorem 1(c), p.49 (random-walk landmarks, amortized).** Aryanfard, Henzinger,
Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space Dynamic Model*, STOC 2027
submission (manuscript sha256 e9b19480…), Theorem 7.9, p.49: "Let c > 0 be a constant, and let n ≥ 2
and 1 ≤ S ≤ n be integers. In the list model, there is a randomized algorithm with space Õ(S) for
Dynamic s-t Connectivity in the incremental setting such that, for every update sequence, with
probability at least 1 − n^{−c}, all of its answers are correct and, for every k ≥ 1, both the total
time and the total number of queries of its first k updates are Õ(k(1 + min{n, k}/S)). Simulating
each list query by a row scan of the adjacency matrix, with O(n) queries and O(1) words, gives the
matrix-model bound of Theorem 1(c)." Theorem 1(c), p.5: "There is an algorithm that, during its first
k updates, for every k ≥ 1, uses space Õ(S) and takes total time Õ(nk(1 + min{n, k}/S)) in the matrix
model and Õ(k(1 + min{n, k}/S)) in the list model."

For every `c > 0` there are `C > 0`, `e, a ∈ ℕ` with `a ≥ 1`, and programs `P_list` and `P_mat` of
the word RAM such that for all `n ≥ 2` and `1 ≤ S ≤ n`, running with `a⌈log₂(n + 1)⌉`-bit words and
writing `L = log₂ n`, for all terminals `s, t` and every insertion-only sequence `σ`:
1. (list model, every sequence of adjacency-list orderings) on every random tape every processed update
   uses space at most `C·S·L^e` words; and the set of random tapes on which some update fails to
   complete with the correct answer, or for some `1 ≤ k ≤ |σ|` the total time or the total number of
   queries of the first `k` updates exceeds `C·k(1 + min{n, k}/S)L^e`, has probability at most
   `n^{−c}`;
2. (matrix model) on every random tape every processed update uses space at most `C·S·L^e` words; and
   the set of random tapes on which some update fails to complete with the correct answer, or for some
   `1 ≤ k ≤ |σ|` the total time of the first `k` updates exceeds `C·n·k(1 + min{n, k}/S)L^e`, has
   probability at most `n^{−c}`.

**Formalization Note.**
1. Machine, `Õ` (exponent written `e` here, as `k` is the prefix length), orderings and probability as
   in Theorem 7.1; as there, the programs are chosen before `n` and `S`, which they receive as input
   words.
2. "An algorithm with space Õ(S)" is stated for every random tape, as in Theorem 7.4.
3. The matrix clause is Theorem 1(c)'s matrix-model bound, which the sentence after Theorem 7.9
   derives; it bounds total time (queries never exceed time). -/
theorem theorem_7_9 :
    ∀ c : ℝ, 0 < c → ∃ (C : ℝ) (e a : ℕ), 0 < C ∧ 1 ≤ a ∧
      ∃ Plist Pmat : Program,
      ∀ n S : ℕ, 2 ≤ n → 1 ≤ S → S ≤ n →
        (∀ (s t : Fin n) (ρ : ℕ → Fin n → Equiv.Perm (Fin n)) (σ : List (PunctSketch.Update n)),
          IsIncremental σ →
          (∀ (ω : ℕ → BitVec (wordSize a n)),
            ∀ r ∈ exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω,
              leR r.space (C * S * Real.logb 2 n ^ e)) ∧
          coinMeasure (wordSize a n)
            {ω | ¬ (AllAnswersCorrect
                (exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) σ s t ∧
              ∀ k : ℕ, 1 ≤ k → k ≤ σ.length →
                leR (((exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω).take
                    k).map UpdStat.time).sum
                  (C * k * (1 + (min n k : ℕ) / (S : ℝ)) * Real.logb 2 n ^ e) ∧
                leR (((exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω).take
                    k).map UpdStat.queries).sum
                  (C * k * (1 + (min n k : ℕ) / (S : ℝ)) * Real.logb 2 n ^ e))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))) ∧
        (∀ (s t : Fin n) (σ : List (PunctSketch.Update n)), IsIncremental σ →
          (∀ (ω : ℕ → BitVec (wordSize a n)),
            ∀ r ∈ exec Pmat (wordSize a n) s t S (fun _ G => matrixReply G) σ ω,
              leR r.space (C * S * Real.logb 2 n ^ e)) ∧
          coinMeasure (wordSize a n)
            {ω | ¬ (AllAnswersCorrect
                (exec Pmat (wordSize a n) s t S (fun _ G => matrixReply G) σ ω) σ s t ∧
              ∀ k : ℕ, 1 ≤ k → k ≤ σ.length →
                leR (((exec Pmat (wordSize a n) s t S (fun _ G => matrixReply G) σ ω).take
                    k).map UpdStat.time).sum
                  (C * n * k * (1 + (min n k : ℕ) / (S : ℝ)) * Real.logb 2 n ^ e))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))) := by sorry

end Supplement

end DynOracleConn
