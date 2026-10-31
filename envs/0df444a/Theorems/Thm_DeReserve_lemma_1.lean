-- Prove2me | Theorems.Thm_DeReserve_lemma_1
-- name    : DeReserve.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:22.603096+00:00
-- url     : https://prove2.me/theorems/8f37007c-8322-41f2-b1de-d5e85e4e769b
-- title:
--   Lemma 1 (p.32): when the backward transfers iteration stops
-- statement:
--   Fix an institution $s$ with capacity vector $q_s=q^1_s$ and priority $\succ_s$, a membership profile $T$ and a set of applicants $A$. Let $q^n_s$ be the capacity vector at iteration $n$ of $C^{BT}_s(A,q_s)$, $N$ its last iteration, $\tau_1$ the number of unfilled OBC positions at the end of iteration 1, $A^{OBC}=\{i\in A:t_i=OBC\}$, and $C^o_s(A,k)$ the $k$ highest-priority acceptable members of $A$. For every iteration $n$ with $1\le n\le N$, $n=N$ if and only if
--
--   1. $\bigl|\bigl(C^o_s(A,(q^n_s)^o)\setminus C^o_s(A,(q^1_s)^o)\bigr)\setminus A^{OBC}\bigr|=\tau_1$, or
--   2. $(q^n_s)^o=(q^1_s)^o+(q^1_s)^{OBC}$.
--
--   The lemma characterizes the stopping iteration and is used in the proofs of substitutability and Pareto dominance.
--
--   Differences from the source:
--   - reading: "N is the last iteration of C^BT_s(A, q_s) iff (1) or (2)" → for every iteration n with 1 ≤ n ≤ N: n = N iff (1) or (2) holds at n; reason: the lemma ranges over the iterations that are performed; after N the capacity vector is constant
--   - encoding: strict linear orders ≻_s on I ∪ {∅} and P_i on S ∪ {∅}; ∅; membership GC → rank bijections Option I ≃ Fin (|I|+1) and Option S ≃ Fin (|S|+1) (rank 0 best); none; none : Option Res; reason: Lean convention; every strict linear order is such a bijection and conversely, so the instances are the same
--   - encoding: C^BT iterates until no OBC seat is vacant → the last iteration is searched among the first q^OBC_s + 1 iterations; reason: q^OBC strictly decreases at every non-final iteration, so the bound is never reached before termination
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, Lemma 1, p.32 (proof pp.32–34)

import Mathlib
import Definitions.Def_DeReserve_Model

namespace DeReserve

/-- **Lemma 1** (when the backward transfers iteration stops). Aygün–Turhan, *How to De-reserve Reserves*, arXiv:2103.05899v5, Lemma 1, p.32.
For an institution `s`, a set of applicants `A` and a membership profile `T`, an iteration
`n` of `C^BT_s(A, q_s)` (`1 ≤ n ≤ N`, `N` the last iteration) is the last one iff
(1) `|(C^o_s(A, (q^n_s)^o) \ C^o_s(A, (q^1_s)^o)) \ A^OBC| = τ_1`, where `τ_1` is the number of
unfilled OBC positions at the end of iteration 1 and `A^OBC = {i ∈ A | t_i = OBC}`, or
(2) `(q^n_s)^o = (q^1_s)^o + (q^1_s)^OBC`.

**Formalization Note.** `iterCaps … n` is `q^n_s` with `q^1_s = q_s`; `lastIter` is `N`;
`openChoice` is `C^o_s`. The paper's "N is the last iteration" ranges over the iterations
actually performed, i.e. `1 ≤ n ≤ N`. -/
theorem lemma_1 {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (q : S → Cap) (pri : S → Priority I) :
    ∀ (s : S) (T : I → CatMembership) (A : Finset I) (n : ℕ),
      1 ≤ n → n ≤ lastIter (pri s) T (q s) A →
      (n = lastIter (pri s) T (q s) A ↔
        (((openChoice (pri s) A (iterCaps (pri s) T (q s) A n .o) \
              openChoice (pri s) A (iterCaps (pri s) T (q s) A 1 .o)) \
              A.filter (fun i => T i = some .OBC)).card =
            vacantOBC (pri s) T A (iterCaps (pri s) T (q s) A 1) ∨
          iterCaps (pri s) T (q s) A n .o =
            iterCaps (pri s) T (q s) A 1 .o + iterCaps (pri s) T (q s) A 1 .OBC)) := by sorry

end DeReserve
