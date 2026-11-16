-- Prove2me | Theorems.Thm_DynOracleConn_Supplement_theorem_7_1
-- name    : DynOracleConn.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:49:13.323206+00:00
-- url     : https://prove2.me/theorems/33085330-5200-4a70-ae67-f1ab23adeb2a
-- title:
--   Theorem 7.1 = Theorem 1(a), pp.43–44 — space $\tilde O(S+\min\{n,i\}/S)$ and worst-case time $\tilde O(n(1+\min\{n,i\}/S))$ (matrix), $\tilde O(\min\{n^2/S^2,1+i/S\})$ (list)
-- statement:
--   For every constant $c>0$ there are constants $C>0$, $k\in\mathbb N$ and $a\ge1$, a matrix-model program $P_{\mathrm{mat}}$ and a list-model program $P_{\mathrm{list}}$ of the word RAM with the following property. Let $n\ge2$ and $1\le S\le n$ be integers, run the programs with words of $a\lceil\log_2(n+1)\rceil$ bits, and write $L=\log_2n$. For all terminals $s,t$, every insertion-only sequence $\sigma$ and, in the list model, every sequence of adjacency-list orderings, with probability at least $1-n^{-c}$ over the random words the following hold.
--
--   1. Every update completes and reports correctly whether $s$ and $t$ are connected after it.
--   2. For every $i$, the space used by the end of the $i$-th update is at most
--   $$C\Big(S+\frac{\min\{n,i\}}{S}\Big)L^k\ \text{ words}.$$
--   3. The $i$-th update takes at most $C\,n\big(1+\min\{n,i\}/S\big)L^k$ steps in the matrix model and at most
--   $$C\min\Big\{\frac{n^2}{S^2},\ 1+\frac iS\Big\}L^k\ \text{ steps}$$
--   in the list model.
--
--   This is the breadth-first-search landmark algorithm. Its space is $\tilde O(S)$ whenever $S\ge\sqrt n$ or $i\le S^2$, and its worst-case matrix time $\tilde O(n^2/S)$ is optimal by Theorem 2.
--
--   **Formalization Note** A step is one executed instruction, oracle calls included. Space counts all memory the program has accessed, both what is kept between updates and the temporary memory used inside an update. Each update's oracle calls see the graph before it.
--
--   Differences from the source:
--   - generalization: "Let n ≥ 2 and 1 ≤ S ≤ n … There is a randomized algorithm" → one program chosen before n and S (after c), which receives n, s, t, S as input words; reason: p.4: "At initialization, the algorithm is given n, s, t, and S"; a single program gives one for each n, S; a program chosen after n could keep the whole graph in its program counter, which is not charged as memory
--   - reading: Õ(·): factors polynomial in log n suppressed (footnote 1, p.1) → ∃ C > 0, k ∈ ℕ chosen after c and before n, S, s, t, i and σ, with the bound multiplied by (log₂ n)^k; reason: the definition of Õ with constants independent of the instance
--   - encoding: the word RAM: words of Θ(log n) bits, time = word operations including oracle calls, space = words of all writable memory → the machine of Supplement.Machine with words of a⌈log₂(n + 1)⌉ bits (a fixed with C, k); time = executed instructions; space = 1 + the largest address accessed, cumulative; reason: the paper names the model and no instruction set; a standard unit-cost instruction set
--   - encoding: with probability at least 1 − n^{−c} → the measure of the failure set is at most n^{−c}; reason: for a non-measurable failure set this bounds its outer measure, so the success event contains a measurable set of probability ≥ 1 − n^{−c}
--   - encoding: "for every update sequence"; guarantees against output-adaptive adversaries → every incremental (valid, insertion-only) sequence and terminals s, t fixed in advance; reason: §7, p.42: the adaptive case reduces to sequences and orderings fixed in advance
--   - encoding: [n]; vertex labels; Neighbor(v, j) outside [d(v)] → vertices coded 0, …, n − 1; Neighbor returns the code w + 1, or 0 outside [d(v)]; reason: Lean conventions; same instances
--   - reading: the list model: neighbors "in an arbitrary ordering" → every sequence of orderings ρ k, one per update, fixed in advance; reason: §7, p.42: "the update sequence and adjacency-list orderings have been fixed in advance"; the guarantees hold for every ordering
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 7.1, pp.43–44; Theorem 1(a), p.5

import Mathlib
import Definitions.Def_DynOracleConn_Supplement_Exec

namespace DynOracleConn

namespace Supplement

/-- **Theorem 7.1 = Theorem 1(a), pp.43–44 (BFS landmarks).** Aryanfard, Henzinger, Kuszmaul,
Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space Dynamic Model*, STOC 2027
submission (manuscript sha256 e9b19480…), Theorem 7.1, pp.43–44 (Theorem 1(a), p.5): "Let c > 0 be
a constant, and let n ≥ 2 and 1 ≤ S ≤ n be integers. There is a randomized algorithm for Dynamic s-t
Connectivity in the incremental setting such that, for every update sequence, with probability at
least 1 − n^{−c}, all of its answers are correct and, during its i-th update, it uses space
Õ(S + min{n, i}/S) and takes worst-case time Õ(n(1 + min{n, i}/S)) in the matrix model and
Õ(min{n²/S², 1 + i/S}) in the list model."

For every `c > 0` there are `C > 0`, `k, a ∈ ℕ` with `a ≥ 1`, and programs `P_mat` (matrix model)
and `P_list` (list model) of the word RAM such that for all `n ≥ 2` and `1 ≤ S ≤ n`, running with
`a⌈log₂(n + 1)⌉`-bit words and writing `L = log₂ n`, for all terminals `s, t` and every
insertion-only sequence `σ` (and, in the list model, every sequence of adjacency-list orderings), the
set of random tapes on which the following fails has probability at most `n^{−c}`: every update
completes and writes the correct answer, and, for every `i` (1-based), the space used by the end of
update `i` is at most `C(S + min{n, i}/S)L^k` words and update `i` takes at most
`C·n(1 + min{n, i}/S)L^k` steps (matrix) or `C·min{n²/S², 1 + i/S}L^k` steps (list).

**Formalization Note.**
1. Machine: the word RAM of `DynOracleConn.Supplement.Machine` (unit-cost word operations,
   oracle calls, independent uniform random words), run by `exec` with snapshot semantics; time is
   the number of executed instructions including oracle calls; space is one more than the largest
   memory address accessed (persistent and temporary memory both count), cumulative from the start.
2. `Õ` suppresses factors polynomial in `log n` (footnote 1, p.1): `C`, `k` and the word-size
   constant `a` are chosen after `c` and before `n`, `S`, `s`, `t`, `i` and the sequence.
   The programs are also chosen before `n` and `S`, which they receive as input words at
   initialization (p.4). A program chosen after `n` could keep the whole graph in its program
   counter, which the machine does not charge as memory.
3. The update sequence and the orderings are fixed in advance (§7, p.42: the guarantees against
   output-adaptive adversaries reduce to this case); orderings may change between updates.
4. The probability is the measure of the failure set, which bounds the outer measure if that set is
   not measurable, so the success event contains a measurable set of probability at least
   `1 − n^{−c}`. -/
theorem theorem_7_1 :
    ∀ c : ℝ, 0 < c → ∃ (C : ℝ) (k a : ℕ), 0 < C ∧ 1 ≤ a ∧
      ∃ Pmat Plist : Program,
      ∀ n S : ℕ, 2 ≤ n → 1 ≤ S → S ≤ n →
        (∀ (s t : Fin n) (σ : List (PunctSketch.Update n)), IsIncremental σ →
          coinMeasure (wordSize a n)
            {ω | ¬ (AllAnswersCorrect
                (exec Pmat (wordSize a n) s t S (fun _ G => matrixReply G) σ ω) σ s t ∧
              ∀ i < σ.length,
                AtUpd (exec Pmat (wordSize a n) s t S (fun _ G => matrixReply G) σ ω) i
                  (fun r =>
                    leR r.space (C * ((S : ℝ) + (min n (i + 1) : ℕ) / S) * Real.logb 2 n ^ k) ∧
                    leR r.time
                      (C * n * (1 + (min n (i + 1) : ℕ) / (S : ℝ)) * Real.logb 2 n ^ k)))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))) ∧
        (∀ (s t : Fin n) (ρ : ℕ → Fin n → Equiv.Perm (Fin n)) (σ : List (PunctSketch.Update n)),
          IsIncremental σ →
          coinMeasure (wordSize a n)
            {ω | ¬ (AllAnswersCorrect
                (exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) σ s t ∧
              ∀ i < σ.length,
                AtUpd (exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) i
                  (fun r =>
                    leR r.space (C * ((S : ℝ) + (min n (i + 1) : ℕ) / S) * Real.logb 2 n ^ k) ∧
                    leR r.time
                      (C * min ((n : ℝ) ^ 2 / (S : ℝ) ^ 2) (1 + (i + 1 : ℕ) / (S : ℝ)) *
                        Real.logb 2 n ^ k)))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))) := by sorry

end Supplement

end DynOracleConn
