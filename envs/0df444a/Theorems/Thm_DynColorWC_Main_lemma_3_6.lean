-- Prove2me | Theorems.Thm_DynColorWC_Main_lemma_3_6
-- name    : DynColorWC.Main.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:47:22.742331+00:00
-- url     : https://prove2.me/theorems/390fb602-618a-42a1-92c0-df22bf9861d2
-- title:
--   Lemma 3.6 — MaxMill: O(log N) worst-case operations, and every counter is below 10T log(NT)
-- statement:
--   Let $T\ge2$ and $N\ge2$ be integers. If $S$ has never contained more than $N$ elements, then
--   1. every counter $c(x)$ is less than $10T\log_2(NT)$, whatever the tie-breaking of the head selections;
--   2. the MaxMill can be implemented on the word RAM so that each operation (including the output and head reselection it may trigger) ends in $O(\log N)$ time in the worst case: one program, with constants fixed before $T$, $N$, the elements and the operations, which on every coin tape outputs exactly the heads of some run of the MaxMill process.
--
--   Differences from the source:
--
--   - generalization: every counter of the MaxMill (as implemented) is less than 10T log(NT) → for every element type, every valid operation sequence with |S| ≤ N throughout and every tie-breaking of the head selection, every counter of a member is < 10T log₂(NT); reason: the potential argument uses only the abstract process; it specializes to the implementation's own tie-breaking
--   - encoding: the MaxMill of §3.3 (ties broken arbitrarily; output after every T calls to increment) → the relation MillStep T: add/increment as printed, k counts increments since the last output, the head is output and removed when k reaches T, and the new head is any remaining element of maximum counter; reason: a relation allows every tie-break
--   - encoding: S has never contained more than N elements → MillValid N along the run: add x only for x ∉ S with |S| + 1 ≤ N, increment x only for x ∈ S; reason: the operations' preconditions of §3.3 and the size bound
--   - encoding: 'can be implemented such that each operation ends in O(log N) time in the worst case' → one DynBrooks word-RAM program and constants K, a fixed before T, N, U and the operations; elements are naturals < U; preprocessing words T, N, U; add x and increment x as the words 0, x and 1, x; word size a⌈log₂(U + NT + 2)⌉; for every coin tape preprocessing completes and, while the operations are valid, the machine follows a run of MillStep, writes exactly the heads it outputs, and each operation takes ≤ K log₂ N steps; reason: the word-RAM reading of §3; elements are identifiers that fit in a word, and 'implemented' means realizing the MaxMill semantics
--   - encoding: log → Real.logb 2; reason: logarithms are base 2 (§3)
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Lemma 3.6, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynColorWC_Main_Model
import Definitions.Def_DynColorWC_Main_MaxMill

namespace DynColorWC.Main

/-- **Lemma 3.6** (Flin and Ghaffari (2026), STOC 2027 submission, sha256 93ebb2ff…3154300e3,
p. 15 (PDF 17)). Let `T ≥ 2`, `N ≥ 2` be integers. If `S` has never contained more than `N` elements,
the MaxMill data structure can be implemented such that each operation ends in `O(log N)` time in the
worst case and every counter `c(x)` is less than `10 T log(NT)` (`log` is base 2).

1. **Counters.** For every element type, every sequence of valid operations from the empty mill along
   which `S` never has more than `N` elements, and **every** tie-breaking of the head selections,
   every counter `c(x)`, `x ∈ S`, is less than `10 T log₂(NT)`.
2. **Implementation.** There are one word-RAM program `P` and constants `K`, `a` (fixed before `T`,
   `N`, the element bound `U` and the operations) such that for all `T, N ≥ 2`, every `U`, every
   operation list and every coin tape (word size `a⌈log₂(U + NT + 2)⌉`): preprocessing on `T, N, U`
   completes, and there are abstract mill states `s_0 = ∅, s_1, …` and outputs such that, as long as
   the operations so far are valid for the abstract states with elements below `U` and `S` of size
   at most `N`, each operation is a step of the MaxMill (`MillStep`), the machine writes exactly the
   head that step outputs, and the operation takes at most `K log₂ N` steps. -/
theorem lemma_3_6 :
    (∀ (α : Type) [DecidableEq α] (T N : ℕ), 2 ≤ T → 2 ≤ N →
      ∀ s : MillState α, MillReach T N s →
        ∀ x ∈ s.S, (s.cnt x : ℝ) < 10 * T * Real.logb 2 ((N : ℝ) * T)) ∧
    (∃ (P : DynBrooks.Program) (K : ℝ) (a : ℕ),
      ∀ (T N U : ℕ), 2 ≤ T → 2 ≤ N →
        ∀ (ops : List (MillOp ℕ)) (ω : ℕ → BitVec (millWordSize a T N U)),
          (DynBrooks.complete P ω (millInit (millWordSize a T N U) T N U)).isSome ∧
          ∃ (ss : ℕ → MillState ℕ) (outs : ℕ → Option ℕ),
            ss 0 = MillState.empty ℕ ∧
            ∀ i (hi : i < ops.length),
              (∀ j (hj : j ≤ i), MillValid N (ss j) ops[j] ∧ ops[j].elem < U) →
                MillStep T (ss i) ops[i] (outs i) (ss (i + 1)) ∧
                millOpOutput P ω T N U ops i = (outs i).toList ∧
                TimeLE (millOpTime P ω T N U ops i) (K * Real.logb 2 N)) := by sorry

end DynColorWC.Main
