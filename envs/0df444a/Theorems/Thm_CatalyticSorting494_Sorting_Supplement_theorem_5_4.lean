-- Prove2me | Theorems.Thm_CatalyticSorting494_Sorting_Supplement_theorem_5_4
-- name    : CatalyticSorting494.Sorting.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:20:28.932944+00:00
-- url     : https://prove2.me/theorems/a245185c-87f1-4573-a336-d474ee00fb41
-- title:
--   Theorem 5.4 — catalytic transducers that sort need $ST=\Omega(n^2)$
-- statement:
--   Let $M$ be a catalytic transducer (a catalytic machine with a write-only one-way output tape, the catalytic tape restored exactly), with catalytic capacity $c(n)$, and let $S,T:\mathbb N\to\mathbb N$. Suppose that for every $n\ge1$, every list of $n$ integers of $b_n=\max(1,\lceil\log_2 n\rceil)$ bits, and every initial catalytic content of length $c(n)$, the machine halts within $T(n)$ steps, uses at most $S(n)$ clean bits, restores the catalytic tape, and leaves on its output tape the list sorted in nondecreasing order (repetitions kept, $b_n$ bits per entry). Then
--
--   $$S(n)\,T(n)\ \ge\ \Omega(n^2),$$
--
--   that is, there are $\varepsilon>0$ and $N$ (depending on $M$) with $S(n)\,T(n)\ge\varepsilon n^2$ for all $n\ge N$.
--
--   The catalytic capacity $c$ is arbitrary. Since the paper's catalytic algorithms sort in $b\,n^{1+o(1)}$ time and $O(\log(n+b))$ clean space with two output passes, this companion theorem shows that one output pass is strictly weaker for catalytic algorithms. Theorem 1.8 of the introduction is the same statement. It is not used in the proof of the sorting corollary.
--
--   Differences from the source:
--   - encoding: ST ≥ Ω(n²) → ∃ ε > 0, ∃ N, ∀ n ≥ N, ε·n² ≤ S(n)·T(n), with ε and N depending on the machine; reason: the meaning of Ω for one algorithm; the proof's count of branching-program nodes includes the machine's finite-control bits
--   - encoding: S and T the clean space and runtime used by the algorithm → any functions S, T bounding the clean space (published cleanSpace, index tapes charged) and the number of steps of every run, for every n ≥ 1, every input list and every initial catalytic content of length c(n), c arbitrary; reason: worst-case resources; bounds above the exact worst case only make the hypothesis weaker
--   - encoding: a length-n list of log(n)-bit integers, output the sorted list → lists of n naturals below 2^b with b = max 1 ⌈log₂ n⌉, written by the published encodeKeys; output sortedOutput (nondecreasing, repetitions kept, b bits each); reason: ⌈log₂ n⌉ bits hold n distinct values, which is all the proof uses; max 1 makes n = 1 meaningful
--   - generalization: transducer output tape of at most 2^{O(S)} bits; output “all the bits up to the head's position” → no bound on the output tape; output = cells strictly left of the head; reason: more machines satisfy the hypothesis, so the lower bound covers the source's machines; the inclusive reading costs one extra head move
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Theorem 5.4, printed p.22 (PDF p.23); same as Theorem 1.8, printed p.4 (PDF p.5); model Definitions 2.1 and 2.3, printed pp.7–9 (PDF pp.8–10)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine
import Definitions.Def_CatalyticSorting494_Sorting_SortingInstance
import Definitions.Def_CatalyticSorting494_Sorting_Supplement_Transducer

open CatalyticSorting494.Sorting

namespace CatalyticSorting494.Sorting.Supplement

/-- Theorem 5.4. Let `M` be a catalytic transducer with catalytic capacity `c n` that, for every
`n ≥ 1`, sorts every list of `n` integers of `max 1 ⌈log₂ n⌉` bits from every initial catalytic
content within `T n` steps and `S n` clean bits, restoring the catalytic tape. Then
`S n · T n ≥ ε n²` for all large `n`, for some `ε > 0` depending on `M`. -/
theorem theorem_5_4 (M : Transducer) (c S T : ℕ → ℕ)
    (hM : ∀ n : ℕ, 1 ≤ n → ∀ keys : List ℕ, IsKeyList n (max 1 (Nat.clog 2 n)) keys →
      ∀ z : List Bool, z.length = c n →
        M.RunsWithin (encodeKeys n (max 1 (Nat.clog 2 n)) keys) z
          (sortedOutput (max 1 (Nat.clog 2 n)) keys) (T n) (S n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ε * (n : ℝ) ^ 2 ≤ (S n : ℝ) * (T n : ℝ) := by sorry

end CatalyticSorting494.Sorting.Supplement
