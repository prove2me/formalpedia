-- Prove2me | Theorems.Thm_DynOracleConn_Supplement_theorem_5
-- name    : DynOracleConn.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:52:00.963912+00:00
-- url     : https://prove2.me/theorems/68994e16-a3d3-4740-8678-f4a4853089ce
-- title:
--   Theorem 5, p.62 — deterministic fully dynamic forests: $O(S)$ words, worst-case time $O(n^2/S)$ (matrix) and $O((n/S)(\Delta+\log S))$ (list)
-- statement:
--   There are constants $C>0$ and $a\ge1$ and two programs $P_{\mathrm{mat}}$ and $P_{\mathrm{list}}$ of the word RAM, neither of which uses random words, with the following property. Let $n\ge2$ and $1\le S\le n$ be integers and run the programs with words of $a\lceil\log_2(n+1)\rceil$ bits. Let $s,t$ be any terminals and $\sigma$ any valid sequence of insertions and deletions under which the graph is a forest after every prefix.
--
--   1. **Matrix model.** Every update completes and reports correctly whether $s$ and $t$ are connected after it. The space used by its end is at most $C\,S$ words, and the update takes at most $C\,n^2/S$ steps.
--   2. **List model**, for every sequence of adjacency-list orderings. Every update completes with the correct answer, and the space used by its end is at most $C\,S$ words. Moreover, for every $\Delta\ge1$ such that the forest has maximum degree at most $\Delta$ after every prefix of $\sigma$, every update takes at most
--   $$C\,\frac nS\big(\Delta+\log_2S\big)\ \text{ steps}.$$
--
--   The algorithm sparsifies Euler-tour trees: it stores only $O(S)$ oriented edges, spaced $\Theta(n/S)$ apart along the canonical Euler tours, and recovers the rest by navigating the forest through the oracle. For $B=\Theta(S\log n)\le\eta n$ bits it matches the fully dynamic lower bound of Theorem 4 up to a logarithmic factor in the matrix model.
--
--   **Formalization Note** A step is one executed instruction, oracle calls included, and space counts all memory accessed. The constants do not depend on $n$, $S$ or $\Delta$, and the list program does not receive $\Delta$. The canonical Euler tours (p.59) do not depend on the list order, so the orderings may change between updates.
--
--   Differences from the source:
--   - generalization: "Let n ≥ 2 and 1 ≤ S ≤ n … There is a deterministic algorithm" → one program per model, chosen before n and S, which receives n, s, t, S as input words; reason: p.4: "At initialization, the algorithm is given n, s, t, and S"; a single program gives one for each n, S; a program chosen after n could keep the whole graph in its program counter, which is not charged as memory
--   - encoding: O(·) → ∃ C > 0 fixed before n, S and Δ (no logarithmic factor); reason: the definition of O with a constant uniform in n, S, Δ
--   - encoding: the word RAM: words of Θ(log n) bits, time = word operations including oracle calls, space = words of all writable memory → the machine of Supplement.Machine with words of a⌈log₂(n + 1)⌉ bits (a fixed with C); time = executed instructions; space = 1 + the largest address accessed, cumulative; reason: the paper names the model and no instruction set; a standard unit-cost instruction set
--   - encoding: a deterministic algorithm → a program without coin instructions; the bounds stated for every random tape; reason: a program without coin instructions does not read the tape
--   - encoding: "Dynamic s-t Connectivity on forests in the fully dynamic setting" → every valid insertion/deletion sequence σ with the graph a forest after every prefix (ForestThroughout), terminals s, t arbitrary (s = t allowed); reason: §7.4, p.59: every G_k is a forest; Algorithm 7 handles s = t
--   - reading: "O((n/S)(∆ + log S)) in the list model if the maximum degree of the forest never exceeds ∆ ≥ 1" → correctness and space O(S) on every forest sequence; the time bound for every Δ ≥ 1 that bounds the maximum degree after every prefix, with log base 2; reason: the algorithm does not depend on Δ; Δ ≤ n − 1 always holds, so correctness and space need no degree assumption; the base of log S is absorbed by C
--   - reading: the list model: neighbors "in an arbitrary ordering" → every sequence of orderings ρ k, one per update, fixed in advance; reason: §7, p.42: "the update sequence and adjacency-list orderings have been fixed in advance"; the guarantees hold for every ordering
--   - encoding: [n]; vertex labels; Neighbor(v, j) outside [d(v)] → vertices coded 0, …, n − 1; Neighbor returns the code w + 1, or 0 outside [d(v)]; reason: Lean conventions; same instances
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Theorem 5, p.62 (also p.7); §7.4, pp.59–62

import Mathlib
import Definitions.Def_DynOracleConn_Supplement_Exec

namespace DynOracleConn

namespace Supplement

/-- **Theorem 5, p.62 (fully dynamic forests).** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska
Williams, *Connectivity in a New Bounded-Space Dynamic Model*, STOC 2027 submission (manuscript sha256
e9b19480…), Theorem 5, p.62 (also p.7): "Let n ≥ 2 and 1 ≤ S ≤ n be integers. There is a
deterministic algorithm for Dynamic s-t Connectivity on forests in the fully dynamic setting that uses
O(S) words of space and takes worst-case time O(n²/S) per update in the matrix model, and
O((n/S)(∆ + log S)) in the list model if the maximum degree of the forest never exceeds ∆ ≥ 1."

There are `C > 0`, `a ≥ 1` and programs `P_mat` and `P_list` of the word RAM, neither containing a
coin instruction, such that for all `n ≥ 2` and `1 ≤ S ≤ n`, running with `a⌈log₂(n + 1)⌉`-bit
words, for all terminals `s, t`, every valid update sequence `σ` (insertions and deletions) under
which the graph is a forest after every prefix, and every random tape:
1. (matrix model) every update completes with the correct answer, uses space at most `C·S` words by
   its end, and takes at most `C·n²/S` steps;
2. (list model, every sequence of adjacency-list orderings) every update completes with the correct
   answer and uses space at most `C·S` words by its end; and for every `∆ ≥ 1` such that the graph has
   maximum degree at most `∆` after every prefix of `σ`, every update takes at most
   `C·(n/S)(∆ + log₂ S)` steps.

**Formalization Note.**
1. Machine and snapshot semantics as in Theorem 7.1; "deterministic" is a program without coin
   instructions, whose run does not depend on the tape.
2. `O(·)` is uniform in `n`, `S` and `∆`: `C` and `a` are fixed before them. The programs are fixed
   before `n` and `S`, which they receive as input words at initialization (p.4); a program chosen
   after `n` could keep the whole forest in its program counter, which the machine does not charge.
   The list program is fixed before `∆` (the algorithm does not receive `∆`).
3. The list bounds hold for every ordering of the adjacency lists, which may change between updates
   (the canonical Euler tours of p.59 do not depend on the list order). -/
theorem theorem_5 :
    ∃ (C : ℝ) (a : ℕ), 0 < C ∧ 1 ≤ a ∧
      ∃ Pmat Plist : Program, NoCoin Pmat ∧ NoCoin Plist ∧
      ∀ n S : ℕ, 2 ≤ n → 1 ≤ S → S ≤ n →
        (∀ (s t : Fin n) (σ : List (PunctSketch.Update n)) (ω : ℕ → BitVec (wordSize a n)),
          PunctSketch.IsValidStream σ → ForestThroughout σ →
          AllAnswersCorrect (exec Pmat (wordSize a n) s t S (fun _ G => matrixReply G) σ ω) σ s t ∧
          ∀ i < σ.length,
            AtUpd (exec Pmat (wordSize a n) s t S (fun _ G => matrixReply G) σ ω) i
              (fun r => leR r.space (C * S) ∧ leR r.time (C * (n : ℝ) ^ 2 / S))) ∧
        (∀ (s t : Fin n) (ρ : ℕ → Fin n → Equiv.Perm (Fin n)) (σ : List (PunctSketch.Update n))
            (ω : ℕ → BitVec (wordSize a n)),
          PunctSketch.IsValidStream σ → ForestThroughout σ →
          AllAnswersCorrect
              (exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) σ s t ∧
            (∀ i < σ.length,
              AtUpd (exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) i
                (fun r => leR r.space (C * S))) ∧
            ∀ Δ : ℕ, 1 ≤ Δ → MaxDegreeLE σ Δ →
              ∀ i < σ.length,
                AtUpd (exec Plist (wordSize a n) s t S (fun k G => listReply (ρ k) G) σ ω) i
                  (fun r => leR r.time (C * ((n : ℝ) / S) * ((Δ : ℝ) + Real.logb 2 S)))) := by sorry

end Supplement

end DynOracleConn
