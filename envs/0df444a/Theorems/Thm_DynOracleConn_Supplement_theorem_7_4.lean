-- Prove2me | Theorems.Thm_DynOracleConn_Supplement_theorem_7_4
-- name    : DynOracleConn.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:49:41.455206+00:00
-- url     : https://prove2.me/theorems/bd248fe1-5f62-4f5c-aad6-2a06e0964710
-- title:
--   Theorem 7.4 = Theorem 1(b), p.46 — list model, space $\tilde O(S)$, worst-case time $\tilde O(1+\min\{n,i\}^2/S^2)$ for the $i$-th update
-- statement:
--   For every constant $c>0$ there are constants $C>0$, $k\in\mathbb N$ and $a\ge1$ and a list-model program $P$ of the word RAM with the following property. Let $n\ge2$ and $1\le S\le n$ be integers, run $P$ with words of $a\lceil\log_2(n+1)\rceil$ bits, and write $L=\log_2n$. For all terminals $s,t$, every sequence of adjacency-list orderings and every insertion-only sequence $\sigma$, the following hold.
--
--   1. On every outcome of the random words, the space used is at most $C\,S\,L^k$ words.
--   2. With probability at least $1-n^{-c}$, every update completes and reports correctly whether $s$ and $t$ are connected, and for every $i$ the $i$-th update takes at most
--   $$C\Big(1+\frac{\min\{n,i\}^2}{S^2}\Big)L^k\ \text{ steps}.$$
--
--   This is the Metropolis-walk landmark algorithm. Its worst-case time is optimal for $S=O(n/\log n)$ by Theorem 3.
--
--   **Formalization Note** A step is one executed instruction, oracle calls included. Space counts all memory the program has accessed. Each update's oracle calls see the graph before it, and the orderings may change between updates.
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
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 7.4, p.46; Theorem 1(b), p.5

import Mathlib
import Definitions.Def_DynOracleConn_Supplement_Exec

namespace DynOracleConn

namespace Supplement

/-- **Theorem 7.4 = Theorem 1(b), p.46 (Metropolis-walk landmarks).** Aryanfard, Henzinger,
Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space Dynamic Model*, STOC 2027
submission (manuscript sha256 e9b19480…), Theorem 7.4, p.46 (Theorem 1(b), p.5): "Let c > 0 be a
constant, and let n ≥ 2 and 1 ≤ S ≤ n be integers. In the list model, there is a randomized algorithm
with space Õ(S) for Dynamic s-t Connectivity in the incremental setting such that, for every update
sequence, with probability at least 1 − n^{−c}, all of its answers are correct and its i-th update
takes worst-case time Õ(1 + min{n, i}²/S²)."

For every `c > 0` there are `C > 0`, `k, a ∈ ℕ` with `a ≥ 1`, and a program `P` of the word RAM
such that for all `n ≥ 2` and `1 ≤ S ≤ n`, running with `a⌈log₂(n + 1)⌉`-bit words and writing
`L = log₂ n`, for all terminals `s, t`, every sequence of adjacency-list orderings and every
insertion-only sequence `σ`:
1. on every random tape, every processed update uses space at most `C·S·L^k` words;
2. the set of random tapes on which some update fails to complete with the correct answer, or some
   update `i` (1-based) takes more than `C(1 + min{n, i}²/S²)L^k` steps, has probability at most
   `n^{−c}`.

**Formalization Note.**
1. Machine, `Õ`, orderings and probability as in Theorem 7.1; as there, the program is chosen before
   `n` and `S`, which it receives as input words.
2. "An algorithm with space Õ(S)" stands outside "with probability at least 1 − n^{−c}", and is
   stated for every random tape (the stronger of the two readings; p.4 says resource bounds hold
   w.h.p. "unless stated otherwise"). For an update that never completes, the space is the supremum
   over its infinite run. -/
theorem theorem_7_4 :
    ∀ c : ℝ, 0 < c → ∃ (C : ℝ) (k a : ℕ), 0 < C ∧ 1 ≤ a ∧
      ∃ P : Program,
      ∀ n S : ℕ, 2 ≤ n → 1 ≤ S → S ≤ n →
        ∀ (s t : Fin n) (ρ : ℕ → Fin n → Equiv.Perm (Fin n)) (σ : List (PunctSketch.Update n)),
          IsIncremental σ →
          (∀ (ω : ℕ → BitVec (wordSize a n)),
            ∀ r ∈ exec P (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω,
              leR r.space (C * S * Real.logb 2 n ^ k)) ∧
          coinMeasure (wordSize a n)
            {ω | ¬ (AllAnswersCorrect
                (exec P (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) σ s t ∧
              ∀ i < σ.length,
                AtUpd (exec P (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) i
                  (fun r => leR r.time
                    (C * (1 + ((min n (i + 1) : ℕ) : ℝ) ^ 2 / (S : ℝ) ^ 2) *
                      Real.logb 2 n ^ k)))}
            ≤ ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end Supplement

end DynOracleConn
